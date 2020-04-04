package tool.analyzers.strategies;

import java.util.List;
import java.util.Map;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import paramwrapper.ParametricModelChecker;
import tool.Analyzer;
import tool.RDGNode;
import tool.analyzers.buildingblocks.Component;
import tool.analyzers.buildingblocks.DerivationFunction;
import tool.analyzers.buildingblocks.PresenceConditions;
import fdtmc.FDTMC;

public class FamilyBasedFirstPhase {
    private static final Logger LOGGER = Logger.getLogger(FamilyBasedFirstPhase.class.getName());

    ParametricModelChecker modelChecker;

    /**
     * LAMBDA_v
     */
    private DerivationFunction<String, FDTMC, FDTMC> derive150Model;


    public FamilyBasedFirstPhase(ParametricModelChecker modelChecker) {
        this.modelChecker = modelChecker;

        derive150Model = DerivationFunction.abstractDerivation(FDTMC::ifThenElse,
                                                               FDTMC::inline,
                                                               new FDTMC());
    }

    /**
     * Computes the reliability expression for the 150% model of the given RDG node,
     * using the given order of nodes for sequential composition.
     *
     * The returned expression has variables encoding the presence/absence of
     * RDG nodes (components).
     *
     * This function implements the family-based first phase of analyses.
     *
     * @see {@link Analyzer.getReliabilityExpression}
     * @param node
     * @return
     */
    public String getReliabilityExpression(List<RDGNode> dependencies) {
        List<Component<FDTMC>> components = RDGNode.toComponentList(dependencies);
        List<String> presenceConditions = components.stream()
                .map(Component::getPresenceCondition)
                .collect(Collectors.toList());

        Map<String, String> pcEquivalence = PresenceConditions.toEquivalenceClasses(presenceConditions);
        FDTMC derived150Model = Component.deriveFromMany(components,
                                                         derive150Model,
                                                         c -> pcEquivalence.get(c.getPresenceCondition()));
        String expression = modelChecker.getReliability(derived150Model);
        LOGGER.info("Parametric model-checking ok...");
        return expression;
    }

}
