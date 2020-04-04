package tool.analyzers.buildingblocks;

import jadd.ADD;
import jadd.UnrecognizedVariableException;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tool.UnknownFeatureException;
import expressionsolver.ExpressionSolver;

public class PresenceConditions {

    public static boolean isPresent(String presenceCondition, Collection<String> configuration, ExpressionSolver expressionSolver) {
        ADD encodedPresenceCondition = expressionSolver.encodeFormula(presenceCondition);
        Double presenceValue;
        try {
            presenceValue = encodedPresenceCondition.eval(configuration.toArray(new String[configuration.size()]));
        } catch (UnrecognizedVariableException e) {
            throw new UnknownFeatureException(e.getVariableName());
        }
        return presenceValue.compareTo(1.0) == 0;
    }

    /**
     * Maps a list of presence conditions into equivalence classes, i.e.,
     * groups of presence conditions which can be deemed equivalent.
     *
     * The equivalence relation in use is string equality.
     *
     * The keys of the returned mapping are presence conditions.
     * The values of the returned mapping are guaranteed to have no special
     * characters, which makes them suitable to use as identifiers.
     * Also, equal lists of presence conditions always yield the same
     * equivalence classes' identifiers.
     *
     * @param presenceConditions
     * @return
     */
    public static Map<String, String> toEquivalenceClasses(List<String> presenceConditions) {
        Map<String, String> classes = new HashMap<String, String>();
        int i = 0;
        for (String pc: presenceConditions) {
            String eqClass = "s"+i;
            if (!classes.containsKey(pc)) {
                classes.put(pc, eqClass);
                i++;
            }
        }
        return classes;
    }

}
