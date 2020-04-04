package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Lifeline extends SequenceDiagramElement{
	
	//Lifeline's attributes 
	private double reliability; //for representing the component's reliability
	
	
	public Lifeline(String name) {
		super(name);
		reliability = 0.999;
	}
	
	
	public double getReliability() {
		return reliability; 
	}
	
	
	public void setReliability(double reliability) {
		this.reliability = reliability;
	}


	@Override
	public Element getDOM(Document doc) {
		Element e = doc.createElement("Lifeline");
		e.setAttribute("name", getName());
		e.setAttribute("reliability", Double.toString(getReliability()));
		return e;
	}
	
}
