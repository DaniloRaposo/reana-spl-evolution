package parsing.SplGeneratorModels;

import java.util.Iterator; 
import java.util.LinkedList;
import java.util.List;
//import java.util.Vector;



import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class ActivityDiagram {

	/**
	 * An activity diagram is composed of a set of ActivityDiagramElements, 
	 * disposed in a sequential order. 
	 */
	private List<ActivityDiagramElement> setOfElements;
	//There is only one startNode at an ActivityDiagram
	private ActivityDiagramElement startNode;
	private String name;  
	
	/**
	 * Method for adding an element into the Activity Diagram, in an sequential
	 * fashion. The element can be a start node, an activity, a transition bet-
	 * ween two elements, a decision node, a merge node and an end node. 
	 * @param e - Activity diagram element being added into the activity diagram
	 * @return True in case the element was successfully added, False in case 
	 * there is already an element equals the element being added. 
	 */
	public boolean addElement(ActivityDiagramElement e) {
		boolean answer = setOfElements.add(e); 
		return answer;
	}
	
	
	
	public ActivityDiagram() {
		startNode = ActivityDiagramElement.createElement(
				ActivityDiagramElement.START_NODE, 
				null);
		setOfElements = new LinkedList<ActivityDiagramElement>();
		setOfElements.add(startNode);
	}



	public ActivityDiagramElement getStartNode() {
		return startNode;
	}



	public boolean containsElement(String elementName) {
		Iterator<ActivityDiagramElement> itElements = setOfElements.iterator();
		ActivityDiagramElement e; 
		
		while(itElements.hasNext()) {
			e = itElements.next(); 
			if (e.getElementName().equals(elementName))
				return true; 
		}
		return false;
	}



	public Activity getActivityByName(String activityName) {
		ActivityDiagramElement e; 
		Activity a = null; 
		Iterator<ActivityDiagramElement> itElements = setOfElements.iterator(); 
		
		while (itElements.hasNext()) {
			e = itElements.next(); 
			if (e.getClass().getName().equals("splGenerator.Activity")){
				if (e.getElementName().equals(activityName))
					a = (Activity) e;
			}
		}
		return a;
	}



	public void setName(String name) {
		this.name = name; 
	}



	public String getName() {
		return name;
	}



	public Element getDOM(Document doc) {
		Element root = null; 
		root = doc.createElement("ActivityDiagram"); 
		root.setAttribute("name", name);
		
		Element elements = null; 
		elements = doc.createElement("Elements");
		
		Element transitions = null; 
		transitions = doc.createElement("Transitions");
		
		
		
		//Create elements for each ActivityDiagramElement in this 
		//ActivityDiagram object.
		Iterator <ActivityDiagramElement>it = setOfElements.iterator();

		Element el; 
		while (it.hasNext()) {
			ActivityDiagramElement ade = it.next();

			if (ade.getClass().getSimpleName().
					equals("Transition")) {
				Transition t = (Transition) ade; 
				el = doc.createElement(t.getClass().getSimpleName());
				el.setAttribute("name", t.getElementName());
				el.setAttribute("probability", Double.toString(t.getProbability()));
				el.setAttribute("source", t.getSource().getElementName());
				el.setAttribute("target", t.getTarget().getElementName());
				transitions.appendChild(el);
			} else {
				el = ade.getDom(doc); 
				elements.appendChild(el);
			}
			
		}
		
		root.appendChild(elements);
		root.appendChild(transitions);
		
		return root;
	}



	public List<Activity> getSetOfActivities() {
		List<Activity> l = new LinkedList<Activity>();
		Iterator<ActivityDiagramElement> it = setOfElements.iterator(); 
		while (it.hasNext()) {
			ActivityDiagramElement e = it.next();
			Activity a = null; 
			if (e.getClass().getSimpleName().equals("Activity")){
				a = (Activity)e;
				l.add(a); 
			}
		}
		return l;
	}



	public void setStartNode(StartNode sn) {
		this.startNode = sn;
	}



	public ActivityDiagramElement getElementByName(String sourceElementName) {
		ActivityDiagramElement answer = null;
		Iterator<ActivityDiagramElement> it = setOfElements.iterator(); 
		while (it.hasNext()) {
			ActivityDiagramElement e = it.next();
			if (e.getElementName().equals(sourceElementName)) {
				answer = e; 
				return answer;
			}
		}
		return answer;
	}



	public static void reset() {
		// TODO Auto-generated method stub
		
	}



	public void removeElement(ActivityDiagramElement element) {
		if (setOfElements.contains(element)){
			setOfElements.remove(element);
		}
		
	}
}
