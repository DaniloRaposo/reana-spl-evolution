package fdtmc;

public class State {

	private String variableName;
	private int index;
	private String label;

	public void setVariableName(String variableName) {
		this.variableName = variableName;
	}

	public void setIndex(int index) {
		this.index = index;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public int getIndex() {
		return index;
	}

	public String getVariableName() {
		return variableName;
	}

	public String getLabel() {
		return label;
	}

    /**
     * A state is equal to another one if they have equal indices.
     * Labels are only considered when comparing FDTMCs as a whole.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof State) {
            State other = (State) obj;
            return this.index == other.index;
        }
        return false;
    }

    @Override
    public int hashCode() {
        return index + 1;
    }

}
