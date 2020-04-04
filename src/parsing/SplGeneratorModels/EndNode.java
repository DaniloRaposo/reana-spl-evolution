package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class EndNode extends ActivityDiagramElement {

	public EndNode() {
		super("End node");
	}

	
	public Element getDom(Document doc) {
		return super.getDom(doc);
	}
}
