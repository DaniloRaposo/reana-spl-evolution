package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class MergeNode extends ActivityDiagramElement{
	
	public MergeNode() {
	
	}
	
	public MergeNode(String elementName) {
		super(elementName);
	}

	
	public Element getDom(Document doc) {
		return super.getDom(doc);
	}

}
