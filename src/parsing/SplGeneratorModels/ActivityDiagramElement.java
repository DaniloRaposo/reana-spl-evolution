package parsing.SplGeneratorModels;

import java.util.HashSet;

import java.util.Iterator;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public abstract class ActivityDiagramElement {

	/**
	 * Object's attributes
	 */
	private String elementName; 
	private HashSet<Transition> transitions;
	private HashSet<String> labels;
	
	/**
	 * Constants for representing each object of Activity Diagram element
	 */
	public static final int START_NODE = 1;
	public static final int ACTIVITY = 2; 
	public static final int TRANSITION = 3; 
	public static final int DECISION_NODE = 4; 
	public static final int MERGE_NODE = 5; 
	public static final int END_NODE = 6;
	
	
	public ActivityDiagramElement() {
		transitions = new HashSet<Transition>();
		labels = new HashSet<String>();
	}
	
	public ActivityDiagramElement(String elementName) {
		this();
		this.elementName = elementName;
	}

	public String getElementName() {
		return elementName;
	}
	
	public void setElementName(String elementName) {
		this.elementName = elementName;
	}
	

	/**
	 * Factory method for creating activity diagram elements, according to the 
	 * constants defined at this class. 
	 * @param elementType - The parameter represents the element being created
	 * @return The activity diagram element created.
	 */
	public static ActivityDiagramElement createElement(int elementType, 
			String elementName) {
		ActivityDiagramElement e; 
		switch (elementType) {
		case START_NODE:
			e = new StartNode();
			e.addLabel("init"); 
			break;

		case ACTIVITY:
			e = new Activity(elementName);
			break;
			
		case TRANSITION:
			e = new Transition(elementName);
			break;
			
		case DECISION_NODE:
			e = new DecisionNode(elementName);
			break;
			
		case MERGE_NODE:
			e = new MergeNode(elementName); 
			break; 
			
		case END_NODE: 
			e = new EndNode();
			e.addLabel("success");
			break; 
			
		default:
			e = null; 
			break;
		}
		return e;
	}


	private boolean addLabel(String l) {
		return labels.add(l);
	}

	public HashSet<Transition> getTransitions() {
		return transitions;
	}

	public Transition getTransitionByName(String name) {
		Iterator<Transition> it = transitions.iterator();
		while (it.hasNext()) {
			Transition t = it.next();
			if (t.getElementName().equals(name))
				return t; 
		}
		return null;
	}

	public boolean addOutgoingTransition(Transition transition) {
		boolean answer = transitions.add(transition);
		return answer;
	}

	public Transition createTransition(ActivityDiagramElement target, 
			String transName, 
			double probability) {
		Transition t = new Transition(transName); 
		t.setTarget(target);
		t.setProbability(probability);
		t.setSource(this);
		this.transitions.add(t);
		return t;
	}

	public HashSet<String> getLabels() {
		return labels;
	}

	
	public Element getDom(Document doc){
		Element root = doc.createElement("ActivityDiagramElement"); 
		root.setAttribute("name", getElementName());
		root.setAttribute("type", this.getClass().getSimpleName());
		return root;
	}

	public static void reset() {
		// TODO Auto-generated method stub
		
	}
	
	
	
	
	
}
