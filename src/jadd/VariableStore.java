package jadd;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

public class VariableStore {
    private Map<String, ADD> variables;
    private SortedMap<Short, String> variableNames;
    private Map<String, Short> variableIndices;

    public VariableStore() {
        variables = new HashMap<String, ADD>();
        variableNames = new TreeMap<Short, String>();
        variableIndices = new HashMap<String, Short>();
    }

    public int getNumberOfVariables() {
        return variables.size();
    }

    public boolean contains(String varName) {
        return variables.containsKey(varName);
    }

    public ADD get(String varName) {
        return variables.get(varName);
    }

    public String getName(short varIndex) {
        return variableNames.get(varIndex);
    }

    public void put(short varIndex, String varName, ADD varADD) {
        variables.put(varName, varADD);
        variableNames.put(varIndex, varName);
        variableIndices.put(varName, varIndex);
    }

    public String[] getOrderedNames() {
        Collection<String> values = variableNames.values();
        return values.toArray(new String[values.size()]);
    }

    /**
     * Returns a 0-1 int[] suitable for CUDD functions which expect arrays
     * which represent presence of variables whose indices have the value 1
     * in the equivalent array indices.
     * @param variables Names of the variables to be included.
     * @return an array with 1 in every position whose index is equal to that
     *          of a present variable and 0 in every other position.
     */
    public int[] toPresenceVector(String[] variables) throws UnrecognizedVariableException {
        int[] presenceVector = new int[variableIndices.size()];
        Arrays.fill(presenceVector, 0);
        for (String var: variables) {
            if (variableIndices.containsKey(var)) {
                int index = variableIndices.get(var);
                presenceVector[index] = 1;
            } else {
                throw new UnrecognizedVariableException(var);
            }
        }
        return presenceVector;
    }

    /**
     * Returns a list of variable names from a corresponding presence vector.
     *
     * Whenever a variable is marked as "don't care", we parenthesize its name
     * to indicate so.
     * @param presenceVector an array of literals, which are integers in {0, 1, 2};
     *          0 represents a complemented literal, 1 represents an uncomplemented
     *          literal, and 2 stands for don't care.
     * @return
     */
    public List<String> fromPresenceVector(int[] presenceVector) {
        List<String> varNames = new LinkedList<String>();
        for (short i = 0; i < presenceVector.length; i++) {
            if (presenceVector[i] == 1) {
                varNames.add(variableNames.get(i));
            } else if (presenceVector[i] == 2) {
                varNames.add("("+variableNames.get(i)+")");
            }
        }
        return varNames;
    }

    /**
     * Returns a permutation vector.
     * The i-th entry of the permutation array contains the index of the
     * variable that should be brought to the i-th level.
     * @param variables Names of the variables in the new order.
     * @return an array with the current index of each variable in the order
     *      specified by {@code variables}.
     */
    public int[] toPermutationVector(String[] variables) throws UnrecognizedVariableException {
        int[] permutationVector = new int[variableIndices.size()];
        int i = 0;
        for (String var: variables) {
            if (variableIndices.containsKey(var)) {
                int index = variableIndices.get(var);
                permutationVector[i] = index;
            } else {
                throw new UnrecognizedVariableException(var);
            }
            i++;
        }
        return permutationVector;
    }

}