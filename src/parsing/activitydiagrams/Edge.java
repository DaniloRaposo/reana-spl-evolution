package parsing.activitydiagrams;

public class Edge {
	private String id;
	private String name;
	private String guard;
	private EdgeType type;
	private Activity source;
	private Activity target;
	private float probability = 1.0f;

	public Edge(String id, String name, String type) {
		this.id = id;
		this.name = name;
		if ("uml:ControlFlow".equals(type)) {
			this.type = EdgeType.CONTROL_FLOW;
		} else if ("uml:ObjectFlow".equals(type)) {
			this.type = EdgeType.OBJECT_FLOW;
		}
	}

	public String getName() {
		return name;
	}

	public String getGuard() {
		return guard;
	}

	public void setGuard(String guard) {
		this.guard = guard;
	}

	public Activity getSource() {
		return source;
	}

	public void setSource(Activity source) {
		this.source = source;
	}

	public Activity getTarget() {
		return target;
	}

	public void setTarget(Activity target) {
		this.target = target;
	}

    public void setProbability(float probability) {
        this.probability = probability;
    }

    public float getProbability() {
        return this.probability;
    }

	public String getId() {
		return id;
	}

	public EdgeType getType() {
		return type;
	}

	public String print() {
		return "Type: " + this.type + "; Name: " + this.name + "; Guard: " + this.guard + "\n";
	}
}
