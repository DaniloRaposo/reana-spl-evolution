package jadd;

/**
 * Exception thrown whenever a variable which is unknown to the JADD runtime
 * is used.
 * @author thiago
 *
 */
public class UnrecognizedVariableException extends Exception {

    /**
     * UUID for warning resolution.
     */
    private static final long serialVersionUID = -6767550900715447808L;
    private final String variableName;

    public UnrecognizedVariableException(String variableName) {
        super("Unrecognized variable: " + variableName);
        this.variableName = variableName;
    }

    public String getVariableName() {
        return variableName;
    }

}
