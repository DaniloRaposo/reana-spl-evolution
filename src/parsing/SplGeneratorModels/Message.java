package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Message extends SequenceDiagramElement{

	//Constants representing message types
	public static final int SYNCHRONOUS = 1; 
	public static final int ASYNCHRONOUS = 2; 
	public static final int REPLY = 3;
	
	// Message's attributes 
	private int type; //synchronous, asynchronous or reply
	private double probability; //for representing channel's and component's
								//realiabilities
	private Lifeline source; 
	private Lifeline target;

	
	public Message(String name) {
		super(name);
	}
	
	public void setProbability (double probability) {
		this.probability = probability; 
	}
	
	public double getProbability () {
		return probability; 
	}
	
	public void setSource(Lifeline source) {
		this.source = source; 
	}
	
	public Lifeline getSource() {
		return source; 
	}
	
	public void setTarget (Lifeline target) {
		this.target = target; 
	}
	
	public Lifeline getTarget() {
		return target; 
	}
	
	public int getType() {
		return type;
	}

	public void setType(int type) {
		this.type = type;
	}

	public Element getDOM(Document doc) {
		Element e = doc.createElement("Message");
		e.setAttribute("name", getName());
		e.setAttribute("probability", Double.toString(getProbability()));
		e.setAttribute("source", source.getName());
		e.setAttribute("target", target.getName());
		switch (type) {
		case SYNCHRONOUS:
			e.setAttribute("type", "synchronous");
			break;

		case ASYNCHRONOUS: 
			e.setAttribute("type", "asynchronous");
			break;
			
		case REPLY: 
			e.setAttribute("type", "reply");
			break;
			
		default:
			break;
		}
//		(type == SYNCHRONOUS ? e.setAttribute("type", "synchronous"):);
//		()
		return e;
	}
	
}
