package parsing.SplGeneratorModels;

import java.util.HashMap;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public abstract class SequenceDiagramElement {

	public static final int LIFELINE = 1;
	public static final int MESSAGE = 2;
	public static final int FRAGMENT = 3;
	public static HashMap<String, SequenceDiagramElement> elements = 
			new HashMap<String, SequenceDiagramElement>();
	
	//Sequence Diagram Element's attributes
	private String name;

	/**
	 * This method creates all the elements that a sequence diagram can use for
	 * representing the software behavior. All the objects created by this class
	 * have type equals to its subclasses, like Lifeline, Message and Fragment. 
	 * For creating an object of such type, it is necessary to inform which 
	 * object to instantiate by the parameter type. This method is a factory 
	 * method. All created elements remains stored in the class. 
	 * @param type The type of the object that will be created. Its value can be
	 * LIFELINE, MESSAGE or FRAGMENT. 
	 * @param name The name of the element that will be created. 
	 * @return the object just created. 
	 */
	public static SequenceDiagramElement createElement(int type, String name) {
		SequenceDiagramElement e = null; 
		switch (type) {
		case LIFELINE:
			e = elements.get(name); 
			if (e == null) {
				e = new Lifeline(name); 
				elements.put(name, e);
			}
			break;

		case MESSAGE:
			e = new Message(name);
			elements.put(name, e);
			break;
			
		case FRAGMENT: 
			e = new Fragment(name); 
			elements.put(name, e);
			
		default:
			break;
		}
		return e;
	} 
	
	public SequenceDiagramElement(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}

	public static SequenceDiagramElement getElementByName(String elementName) {
		return elements.get(elementName);
	}

	public abstract Element getDOM(Document doc) ;

	public static void reset() {
		elements.clear();
	}

	public static int countLifelines() {
		int answer = 0;
		for (String key : elements.keySet()) {
			SequenceDiagramElement sde = elements.get(key); 
			if (sde instanceof Lifeline) {
				Lifeline l = (Lifeline) sde;
				System.out.println(l.getName() + ":" + l.getReliability());
				answer++; 
			}
		}
		return answer;
	} 
	
}
