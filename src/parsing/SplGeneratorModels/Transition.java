package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Transition extends ActivityDiagramElement{

	private ActivityDiagramElement source;
	private ActivityDiagramElement target;
	private double probability;

	public Transition(){
		
	}
	
	public Transition (String elementName){
		super(elementName);
	}
	
	public void setSource(ActivityDiagramElement source) {
		this.source = source;
		source.addOutgoingTransition(this);
	}
	
	public ActivityDiagramElement getSource() {
		return source;
	}
	
	public void setTarget(ActivityDiagramElement target) {
		this.target = target;
	}
	
	public ActivityDiagramElement getTarget() {
		return target;
	}
	
	public void setProbability(double probability) {
		this.probability = probability;
	}
	
	public double getProbability() {
		return this.probability;
	}

	@Override
	public Element getDom(Document d) {
		// TODO Auto-generated method stub
		return null;
	}
}
