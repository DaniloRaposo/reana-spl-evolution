package parsing;

public abstract class Node {
	private String id;
	ProbabilityEnergyTimeProfile profile = new ProbabilityEnergyTimeProfile();

	public Node(String id) {
		this.id = id;
	}

	public void setProfile(ProbabilityEnergyTimeProfile profile) {
	    this.profile = profile;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		Node other = (Node) obj;
		if (this.id == null) {
			if (other.id != null) {
				return false;
			}
		} else if (!this.id.equals(other.id)) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
	    if (this.id != null) {
	        return (this.id + this.getClass()).hashCode();
	    } else {
	        return 0;
	    }
	}

	public float getEnergy() {
		return this.profile.getEnergy();
	}

	public float getExecTime() {
		return this.profile.getExecTime();
	}

	public String getId() {
		return this.id;
	}

	public boolean hasEnergy() {
		return this.profile.hasEnergy();
	}

	public boolean hasExecTime() {
		return this.profile.hasExecTime();
	}

	public boolean hasProb() {
		return this.profile.hasProbability();
	}

	public float getProb() {
		return this.profile.getProbability();
	}

}
