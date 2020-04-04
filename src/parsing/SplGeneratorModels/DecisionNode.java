package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class DecisionNode extends ActivityDiagramElement{

	public DecisionNode() {
		
	}

	public DecisionNode(String elementName) {
		super(elementName);
	}

	
	public Element getDom(Document doc) {
		return super.getDom(doc);
	}

}
