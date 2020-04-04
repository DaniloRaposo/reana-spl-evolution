package fdtmc;

/**
 * Represents an abstracted away FDTMC fragment.
 *
 * @author thiago
 */
public class Interface {
    private String abstractedId;
    private State initial;
    private State success;
    private State error;
    private Transition successTransition;
    private Transition errorTransition;

    public Interface(String abstractedId, State initial, State success, State error, Transition successTransition, Transition errorTransition) {
        this.abstractedId = abstractedId;
        this.initial = initial;
        this.success = success;
        this.error = error;
        this.successTransition = successTransition;
        this.errorTransition = errorTransition;
    }

    public State getInitial() {
        return initial;
    }

    public State getSuccess() {
        return success;
    }

    public State getError() {
        return error;
    }

    public Transition getSuccessTransition() {
        return successTransition;
    }

    public Transition getErrorTransition() {
        return errorTransition;
    }

    public String getAbstractedId() {
        return abstractedId;
    }

    /**
     * Interfaces are compared for equality disregarding the abstracted id.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Interface) {
            Interface other = (Interface) obj;
            return initial.equals(other.initial)
                    && success.equals(other.success)
                    && error.equals(other.error)
                    && successTransition.equals(other.successTransition)
                    && errorTransition.equals(other.errorTransition);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return initial.hashCode()
                + success.hashCode()
                + error.hashCode()
                + successTransition.hashCode()
                + errorTransition.hashCode();
    }

}
