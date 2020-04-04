package parsing.SplGeneratorModels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class StartNode extends ActivityDiagramElement{

	public StartNode() {
		super("Start node");
	}
	
	@Override
	public Element getDom(Document doc) {
		return super.getDom(doc);
//		Document doc = d;
//		Element root = null; 
//		
//		root = doc.createElement("ActivityDiagramElement");
//		root.setAttribute("name", getElementName());
//		root.setAttribute("type", "startNode");
//		
//		return root;
	}
}
