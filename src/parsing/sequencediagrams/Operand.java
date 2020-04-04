package parsing.sequencediagrams;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import parsing.Node;

public class Operand extends Node {
	// Attributes

		private String guard;
		private List<Node> nodes;
		private Map<String, Node> nodeById;

	// Constructors

		public Operand(String id) {
			super(id);
			nodes = new ArrayList<Node>();
			nodeById = new HashMap<String, Node>();
		}

	// Relevant Methods

		public void addNode(Node node) {
			this.nodes.add(node);
			this.nodeById.put(node.getId(), node);
		}

	// Getters and Setters

		public String getGuard() {
			return guard;
		}

		public void setGuard(String guard) {
			this.guard = guard;
		}

		public List<Node> getNodes() {
			return nodes;
		}

		@Override
		public boolean equals(Object obj) {
		    return super.equals(obj) && guard.equals(((Operand) obj).guard);
		}

		@Override
		public int hashCode() {
		    return (this.getId() + this.getClass() + this.guard).hashCode();
		}
}
