package parsing.SplGeneratorModels;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class SequenceDiagram {
	
	//Static elements
	private static HashMap<String, SequenceDiagram> sequenceDiagrams = 
			new HashMap<String, SequenceDiagram>(); 
	
	//Sequence diagram attributes
	private String name; 
	private String guardCondition; 
	private HashSet<Lifeline> lifelines; 
	private LinkedList<SequenceDiagramElement> elements;

	public static SequenceDiagram createSequenceDiagram(String name, String guard) {
		SequenceDiagram answer; 
		if (sequenceDiagrams.containsKey(name)) { 
			answer = sequenceDiagrams.get(name);
//			System.out.println("Achei SD " + answer.getName() + " " + answer.getGuardCondition());
//			if (answer.guardCondition != guard) {
			if (answer.guardCondition == null) {
				System.out.println("Setei guarda");
				answer.setGuard(guard);
			}
		} else {
			answer = new SequenceDiagram(name, guard);
//			System.out.println("Criei SD " + answer.getName() + " " + answer.getGuardCondition());
			sequenceDiagrams.put(name, answer);
		}
		
		return answer;
//		SequenceDiagram temp = new SequenceDiagram(name, guard);
//		sequenceDiagrams.put(name, temp);
//			return temp; 
//		else 
//			return null;
	}


	public static SequenceDiagram getSequenceDiagramByName (String name) {
		SequenceDiagram s = sequenceDiagrams.get(name);
		return s; 
	}
	
	
	private SequenceDiagram() {
		lifelines = new HashSet<Lifeline>();
		elements = new LinkedList<SequenceDiagramElement>();
	}
	
	private SequenceDiagram(String name, String guard) {
		this();
		this.name = name;
		this.guardCondition = guard;
	}

	
	public void setGuard(String guard) {
		guardCondition = guard;
	}


	public Lifeline createLifeline(String name) {
		Lifeline l = (Lifeline) SequenceDiagramElement.createElement(
				SequenceDiagramElement.LIFELINE, name);
		boolean inserted = lifelines.add(l);
		if (inserted)
			return l;
		else 
			return null;
	}


	public String getName() {
		return name;
	}


	public String getGuardCondition() {
		return guardCondition;
	}


	public boolean containsLifeline(String lifelineName) {
		Iterator<Lifeline> it = lifelines.iterator();
		while (it.hasNext()) {
			Lifeline l = it.next();
			if (l.getName().equals(lifelineName))
				return true;
		}
		return false;
	}


	public Message createMessage(Lifeline source, Lifeline target, int type, 
			String name, double probability) {
		SequenceDiagramElement e = SequenceDiagramElement.createElement(
				SequenceDiagramElement.MESSAGE, name);
		//Check if source and target lifelines are part of the sequence diagram
		if (!lifelines.contains(source))
			lifelines.add(source);
		if (!lifelines.contains(target))
			lifelines.add(target);
		//Create the message object
		Message m = (Message) e;
		m.setType(type);
		m.setSource(source);
		m.setTarget(target);
		m.setProbability(probability);
		
		boolean answer = elements.add(m);
		if (answer)
			return m;
		else
			return null;
	}


	public LinkedList<SequenceDiagramElement> getElements() {
		return elements;
	}


	public Fragment createFragment(int type, String name) {
		SequenceDiagramElement e = SequenceDiagramElement.createElement(
				SequenceDiagramElement.FRAGMENT, name);
		Fragment f = (Fragment) e; 
		f.setType(type);
		
		boolean answer = elements.add(f);
		if (answer) 
			return f;
		else 
			return null;
	}
	
	
	public Element getDOM(Document doc) {
		Element root = doc.createElement("SequenceDiagram"); 
		root.setAttribute("name", getName());
		root.setAttribute("guard", getGuardCondition());
		
		Iterator<SequenceDiagramElement> ite = elements.iterator(); 
		while(ite.hasNext()) {
			SequenceDiagramElement el = ite.next(); 
			Element e = el.getDOM(doc); 
			root.appendChild(e);
		}
		
		return root; 
	}
	


	public HashSet<Lifeline> getLifelines() {
		return lifelines;
	}


	public HashSet<Fragment> getFragments() {
		HashSet<Fragment> setOfFragments = new HashSet<Fragment>(); 
		Iterator<SequenceDiagramElement> it = elements.iterator(); 
		while (it.hasNext()) {
			SequenceDiagramElement e = it.next();
			if (e.getClass().getSimpleName().equals("Fragment")) {
				Fragment f = (Fragment) e; 
				setOfFragments.add(f); 
			}
		}
		return setOfFragments;
	}


	
	public LinkedList<SequenceDiagram> getTransitiveSequenceDiagram() {
		LinkedList<SequenceDiagram> answer = new LinkedList<SequenceDiagram>();
		HashSet<Fragment> fragments = getFragments(); 
		Iterator<Fragment> itf = fragments.iterator();
		while (itf.hasNext()) {
			Fragment f = itf.next(); 
			answer.addAll(f.getTransitiveSequenceDiagram());
		}
		return answer;
	}


	public HashSet<Lifeline> getTransitiveLifeline() {
		HashSet<Lifeline> answer = new HashSet<Lifeline>(); 
		answer.addAll(lifelines);
		//For each fragment in the sequence diagram, we should get its sequence diagrams.
		Iterator<Fragment> itFrag = getFragments().iterator();
		while (itFrag.hasNext()) {
			Fragment f = itFrag.next(); 
			answer.addAll(f.getTransitiveLifeline()); 
		}
		return answer;
	}


	public HashSet<Fragment> getTransitiveFragments() {
		HashSet<Fragment> answer = new HashSet<Fragment>();
		answer.addAll(getFragments());
		
		Iterator<Fragment> itf = getFragments().iterator(); 
		while (itf.hasNext()) {
			Fragment f = itf.next(); 
			answer.addAll(f.getTransitiveFragments()); 
		}
		
		return answer;
	}


	public SequenceDiagramElement getMessageByName(String name) {
		SequenceDiagramElement answer = null; 
		Iterator<SequenceDiagramElement> it = elements.iterator(); 
		while (it.hasNext()) {
			SequenceDiagramElement e = it.next();
			if (e.getName().equals(name)){
				answer = e; 
				break; 
			}
		}
		return answer;
	}


	public Fragment addFragment(Fragment frag) {
		boolean answer = elements.add(frag); 
		if (answer) 
			return frag;
		else 
			return null;		
	}


	public static void reset() {
		// TODO Auto-generated method stub
		sequenceDiagrams.clear(); 
	}
}
