package parsing.sequencediagrams;

import java.util.ArrayList;
import java.util.List;

import parsing.Node;
import parsing.exceptions.UnsupportedFragmentTypeException;

public class Fragment extends Node {

	// Atributos
		private String name;
		private FragmentType type;
		private List<Node> nodes;
		private List<Lifeline> lifelines;

	// Construtores
		public Fragment(String id) {
			super(id);
			name = "";
			type = null;
			nodes = new ArrayList<Node>();
			lifelines = new ArrayList<Lifeline>();
		}

		public Fragment(String id, FragmentType type) {
			this(id);
			this.type = type;
		}

		public Fragment(String id, String name) {
			this(id);
			this.name = name;
		}

		public Fragment(String id, String typeName, String name) throws UnsupportedFragmentTypeException {
			this(id, FragmentType.getType(typeName));
			this.name = name;
		}

	// Métodos relevantes
		public void setType(String typeName) throws UnsupportedFragmentTypeException{
			this.setType(FragmentType.getType(typeName));
		}

		public void addLifeline(Lifeline toAdd) {
			lifelines.add(toAdd);
		}

		public void addNode(Node toAdd) {
			nodes.add(toAdd);
		}


	// Getters e Setters
		public String getName() {
			return name;
		}

		public void setName(String name) {
			this.name = name;
		}

		public FragmentType getType() {
			return type;
		}

		public void setType(FragmentType type) {
			this.type = type;
		}

		public List<Node> getNodes() {
			return nodes;
		}

		public void setNodes(List<Node> nodes) {
			this.nodes = nodes;
		}

		public List<Lifeline> getLifelines() {
			return lifelines;
		}

		public void setLifelines(List<Lifeline> lifelines2) {
			this.lifelines = lifelines2;
		}

		@Override
		public boolean equals(Object obj) {
		    return super.equals(obj) && ((Fragment) obj).type == this.type;
		}

		@Override
		public int hashCode() {
		    return (this.getId() + this.getClass() + this.type).hashCode();
		}
}
