package tool.analyzers.strategies;

import jadd.ADD;
import jadd.JADD;

import java.util.List;
import java.util.Map;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import paramwrapper.ParametricModelChecker;
import tool.CyclicRdgException;
import tool.RDGNode;
import tool.UnknownFeatureException;
import tool.analyzers.ADDReliabilityResults;
import tool.analyzers.IReliabilityAnalysisResults;
import tool.analyzers.buildingblocks.ConcurrencyStrategy;
import tool.analyzers.buildingblocks.FamilyBasedHelper;
import tool.analyzers.buildingblocks.PresenceConditions;
import tool.stats.CollectibleTimers;
import tool.stats.IFormulaCollector;
import tool.stats.ITimeCollector;
import expressionsolver.Expression;
import expressionsolver.ExpressionSolver;

/**
 * Orchestrator of family-based analyses.
 */
public class FamilyBasedAnalyzer {
    private static final Logger LOGGER = Logger.getLogger(FamilyBasedAnalyzer.class.getName());

    private ADD featureModel;
    private ExpressionSolver expressionSolver;
    ParametricModelChecker modelChecker;

    private FamilyBasedFirstPhase firstPhase;
    private FamilyBasedHelper helper;

    private ITimeCollector timeCollector;
    private IFormulaCollector formulaCollector;

    public FamilyBasedAnalyzer(JADD jadd,
                               ADD featureModel,
                               ParametricModelChecker modelChecker,
                               ITimeCollector timeCollector,
                               IFormulaCollector formulaCollector) {
        this.expressionSolver = new ExpressionSolver(jadd);
        this.featureModel = featureModel;
        this.modelChecker = modelChecker;

        this.timeCollector = timeCollector;
        this.formulaCollector = formulaCollector;

        this.firstPhase = new FamilyBasedFirstPhase(modelChecker);
        this.helper = new FamilyBasedHelper(expressionSolver);
    }

    /**
     * Evaluates the family-based reliability function of an RDG node.
     *
     * @param node RDG node whose reliability is to be evaluated.
     * @param concurrencyStrategy
     * @return
     * @throws CyclicRdgException
     */
    public IReliabilityAnalysisResults evaluateReliability(RDGNode node, ConcurrencyStrategy concurrencyStrategy) throws CyclicRdgException, UnknownFeatureException {
        LOGGER.warning("Family-based analysis does not support parallel execution.");
        List<RDGNode> dependencies = node.getDependenciesTransitiveClosure();

        timeCollector.startTimer(CollectibleTimers.MODEL_CHECKING_TIME);
        // Lambda_v + alpha_v
        String expression = firstPhase.getReliabilityExpression(dependencies);
        formulaCollector.collectFormula(node, expression);
        timeCollector.stopTimer(CollectibleTimers.MODEL_CHECKING_TIME);

        timeCollector.startTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);
        // Lift
        Expression<ADD> liftedExpression = helper.lift(expression);

        List<String> presenceConditions = dependencies.stream()
                .map(RDGNode::getPresenceCondition)
                .collect(Collectors.toList());
        Map<String, String> pcEquivalence = PresenceConditions.toEquivalenceClasses(presenceConditions);
        Map<String, String> eqClassToPC = pcEquivalence.entrySet().stream()
                .collect(Collectors.toMap(e -> e.getValue(),
                                          e -> e.getKey(),
                                          (a, b) -> a));

        Map<String, ADD> values = eqClassToPC.entrySet().stream()
                .collect(Collectors.toMap(e -> e.getKey(),
                                          e -> expressionSolver.encodeFormula(e.getValue())));

        // Sigma'_v
        ADD reliability = liftedExpression.solve(values);
        ADD result = featureModel.times(reliability);

        timeCollector.stopTimer(CollectibleTimers.EXPRESSION_SOLVING_TIME);
        LOGGER.info("Formula evaluation ok...");

        return new ADDReliabilityResults(result);
    }

}
