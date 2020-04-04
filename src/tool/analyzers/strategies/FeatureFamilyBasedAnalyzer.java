package tool.analyzers.strategies;

import jadd.ADD;
import jadd.JADD;

import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.stream.Collectors;

import paramwrapper.ParametricModelChecker;
import tool.CyclicRdgException;
import tool.RDGNode;
import tool.analyzers.ADDReliabilityResults;
import tool.analyzers.IPruningStrategy;
import tool.analyzers.IReliabilityAnalysisResults;
import tool.analyzers.NoPruningStrategy;
import tool.analyzers.buildingblocks.AssetProcessor;
import tool.analyzers.buildingblocks.Component;
import tool.analyzers.buildingblocks.ConcurrencyStrategy;
import tool.analyzers.buildingblocks.DerivationFunction;
import tool.analyzers.buildingblocks.FamilyBasedHelper;
import tool.stats.CollectibleTimers;
import tool.stats.IFormulaCollector;
import tool.stats.ITimeCollector;
import expressionsolver.Expression;
import expressionsolver.ExpressionSolver;

/**
 * Orchestrator of feature-family-based analyses.
 */
public class FeatureFamilyBasedAnalyzer {

    private ADD featureModel;
    private JADD jadd;
    private ExpressionSolver expressionSolver;
    private IPruningStrategy pruningStrategy;

    private FeatureBasedFirstPhase firstPhase;
    private FamilyBasedHelper helper;

    /**
     * Sigma_v
     */
    private DerivationFunction<ADD, Expression<ADD>, ADD> solve;


    private ITimeCollector timeCollector;

    public FeatureFamilyBasedAnalyzer(JADD jadd,
                                      ADD featureModel,
                                      ParametricModelChecker modelChecker,
                                      ITimeCollector timeCollector,
                                      IFormulaCollector formulaCollector) {
        this.expressionSolver = new ExpressionSolver(jadd);
        this.jadd = jadd;
        this.featureModel = featureModel;

        this.timeCollector = timeCollector;
        this.pruningStrategy = new NoPruningStrategy();

        this.firstPhase = new FeatureBasedFirstPhase(modelChecker,
                                                     formulaCollector);
        this.helper = new FamilyBasedHelper(expressionSolver);

        AssetProcessor<Expression<ADD>, ADD> evalAndPrune = (expr, values) -> {
            return this.pruningStrategy.pruneInvalidConfigurations(null,
                                                                   expr.solve(values),
                                                                   featureModel);
        };
        solve = DerivationFunction.abstractDerivation(ADD::ite,
                                                      evalAndPrune,
                                                      jadd.makeConstant(1.0));
    }

    /**
     * Evaluates the feature-family-based reliability function of an RDG node, based
     * on the reliabilities of the nodes on which it depends.
     *
     * A reliability function is a boolean function from the set of features
     * to Real values, where the reliability of any invalid configuration is 0.
     *
     * @param node RDG node whose reliability is to be evaluated.
     * @param concurrencyStrategy
     * @param dotOutput path at where to dump the resulting ADD as a dot file.
     * @return
     * @throws CyclicRdgException
     */
    public IReliabilityAnalysisResults evaluateReliability(RDGNode node, ConcurrencyStrategy concurrencyStrategy, String dotOutput) throws CyclicRdgException {
        List<RDGNode> dependencies = node.getDependenciesTransitiveClosure();

        timeCollector.startTimer(CollectibleTimers.MODEL_CHECKING_TIME);
        // Alpha_v
        List<Component<String>> expressions = firstPhase.getReliabilityExpressions(dependencies, concurrencyStrategy);
        timeCollector.stopTimer(CollectibleTimers.MODEL_CHECKING_TIME);

        timeCollector.startTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);
        // Lift
        List<Component<Expression<ADD>>> liftedExpressions = expressions.stream()
                .map(helper::lift)
                .collect(Collectors.toList());
        // Sigma_v
        ADD reliability = solveFromMany(liftedExpressions);
        ADD result = featureModel.times(reliability);
        timeCollector.stopTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);

        if (dotOutput != null) {
            generateDotFile(result, dotOutput);
        }

        return new ADDReliabilityResults(result);
    }

    public IReliabilityAnalysisResults evaluateReliabilityWithEvolution(RDGNode node, ConcurrencyStrategy concurrencyStrategy, String dotOutput, String idFragment) throws CyclicRdgException {
        List<RDGNode> dependencies = node.getDependenciesTransitiveClosure();

        List<Component<String>> expressions = firstPhase.getReliabilityExpressions(dependencies, concurrencyStrategy);

        List<Component<Expression<ADD>>> liftedExpressions = expressions.stream()
                .map(helper::lift)
                .collect(Collectors.toList());
        /* criação dos ADDs para serem usados como se fossem os ADDs calculados
        * em uma etapa anterior. A adoção de um Map ao invés de uma lista se da
        * pois tendo uma lista de ADDs não teriamos como saber qual fragmento
        * cada ADD representa
        */
        Map<String, ADD> addMap = getADDMap(liftedExpressions);// ao invés de retornar um unico add, ele vai retornar a lista com todos os adds gerados
//------------------------------------------------------------------------------
        List<RDGNode> modifiedNodes = getModifiedNodes(node, idFragment);

        timeCollector.startTimer(CollectibleTimers.MODEL_CHECKING_TIME);
        // Alpha_v
        List<Component<String>> newExpressions = firstPhase.getReliabilityExpressions(modifiedNodes, concurrencyStrategy);
        timeCollector.stopTimer(CollectibleTimers.MODEL_CHECKING_TIME);

        timeCollector.startTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);
        // Lift
        List<Component<Expression<ADD>>> newLiftedExpressions = newExpressions.stream()
                .map(helper::lift)
                .collect(Collectors.toList());
        // Sigma_v
        ADD reliability = newSolveFromMany(newLiftedExpressions, addMap);
        ADD result = featureModel.times(reliability);

        timeCollector.stopTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);
        if (dotOutput != null) {
            generateDotFile(result, dotOutput);
        }

        return new ADDReliabilityResults(result);
    }

    private static List<RDGNode> getModifiedNodes(RDGNode root,String idFragment){
        List<RDGNode> nodes = new LinkedList();
        RDGNode auxnode = getNodeInDependencies(root,"Capture");
        nodes.add(getNodeInDependencies(auxnode, idFragment));
        nodes.add(auxnode);
        nodes.add(root);
        return nodes;
    }

    private static RDGNode getNodeInDependencies(RDGNode node, String id){
        Iterator<RDGNode> itr = node.getDependencies().iterator();
        while(itr.hasNext()){
            RDGNode auxnode = itr.next();
            if (auxnode.getId().equals(id))
                return auxnode;
        }
        return null;
    }

    /**
     * Sets the pruning strategy to be used for preventing calculation
     * of reliability values for invalid configurations.
     *
     * If none is set, the default behavior is to multiply the reliability
     * mappings by the feature model's 0,1-ADD (so that valid configurations
     * yield the same reliability, but invalid ones yield 0).
     *
     * @param pruningStrategy the pruningStrategy to set
     */
    public void setPruningStrategy(IPruningStrategy pruningStrategy) {
        this.pruningStrategy = pruningStrategy;
    }

    /**
     * Dumps the computed family reliability function to the output file
     * in the specified path.
     *
     * @param familyReliability Reliability function computed by a call to the
     *          {@link #evaluateFeatureFamilyBasedReliability(RDGNode)} method.
     * @param outputFile Path to the .dot file to be generated.
     */
    public void generateDotFile(ADD familyReliability, String outputFile) {
        jadd.dumpDot("Family Reliability", familyReliability, outputFile);
    }

    private ADD solveFromMany(List<Component<Expression<ADD>>> dependencies) {
        return Component.deriveFromMany(dependencies,
                                        solve,
                                        c -> expressionSolver.encodeFormula(c.getPresenceCondition()));
    }

    private ADD newSolveFromMany(List<Component<Expression<ADD>>> dependencies, Map<String, ADD> addMap) {
        return Component.newDeriveFromMany(dependencies,
                                        solve,
                                        c -> expressionSolver.encodeFormula(c.getPresenceCondition()), addMap);
    }

    private Map<String, ADD> getADDMap(List<Component<Expression<ADD>>> dependencies){
      return Component.getADDMap(dependencies,
                                      solve,
                                      c -> expressionSolver.encodeFormula(c.getPresenceCondition()));
    }

}
