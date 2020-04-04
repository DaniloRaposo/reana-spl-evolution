package parsing.SplGeneratorModels;

import java.util.HashMap;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import parsing.SplGeneratorModels.Fragment;
import parsing.SplGeneratorModels.Lifeline;
import parsing.SplGeneratorModels.Message;
import parsing.SplGeneratorModels.SequenceDiagram;
import parsing.SplGeneratorModels.SequenceDiagramElement;

public class SequenceDiagramParser {

	static HashMap<String, Lifeline> lifelineById;
	static HashMap<String, SequenceDiagram> seqDiagById;
	static HashMap<String, Fragment> fragmentById;

	public static void parse(Document doc) {
		lifelineById = new HashMap<String, Lifeline>();
		seqDiagById = new HashMap<String, SequenceDiagram>();

		// initially parse the lifelines used by the sequence diagrams.
		parseAllLifelines(doc);

		// parse the sequence diagrams (and its children) and then recreate the
		// sequence diagrams in memory
		parseAllSequenceDiagrams(doc);

		// parsing the fragments used by the sequence diagrams.
		parseAllFragments(doc);
	}

	private static void parseAllSequenceDiagrams(Document doc) {
		NodeList listOfSeqDiags = doc.getElementsByTagName("SequenceDiagram");
		for (int i = 0; i < listOfSeqDiags.getLength(); i++) {
			Element seqDiag = (Element) listOfSeqDiags.item(i);
			NamedNodeMap seqDiagAttributes = seqDiag.getAttributes();
			String seqDiagName = seqDiagAttributes.getNamedItem("name")
					.getNodeValue();
			String seqDiagGuard = seqDiagAttributes.getNamedItem("guard")
					.getNodeValue();

			SequenceDiagram sd = SequenceDiagram.createSequenceDiagram(
					seqDiagName, seqDiagGuard);

			// For each message of the sequence diagram, we create it in memory
			NodeList seqDiagChildren = seqDiag.getChildNodes();
			for (int j = 0; j < seqDiagChildren.getLength(); j++) {
				Node n = seqDiagChildren.item(j);
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getNodeName().equals("Message")) {
					Element e = (Element) n;
					String messageName = e.getAttribute("name");
					String probability = e.getAttribute("probability");
					String sourceName = e.getAttribute("source");
					String targetName = e.getAttribute("target");
					int type;
					switch (e.getAttribute("type")) {
					case "asynchronous":
						type = Message.ASYNCHRONOUS;
						break;

					case "synchronous":
						type = Message.SYNCHRONOUS;
						break;

					case "reply":
						type = Message.REPLY;
						break;

					default:
						type = -1;
						System.out.println("Message type is not defined.");
						break;
					}

					Lifeline source = (Lifeline) SequenceDiagramElement
							.getElementByName(sourceName);
					Lifeline target = (Lifeline) SequenceDiagramElement
							.getElementByName(targetName);

					sd.createMessage(source, target, type, messageName,
							Double.parseDouble(probability));
				} else if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getNodeName().equals("Fragment")) {
					parseFragment(sd, n);
				}
			}

			// Add the sequence diagram into the set of sequence diagram created
			// for the SPL
			seqDiagById.put(sd.getName(), sd);
		}
	}

	private static void parseFragment(SequenceDiagram sd, Node n) {
		Element e = (Element) n;
		String fragName = e.getAttribute("name");
		Fragment f = (Fragment) SequenceDiagramElement
				.getElementByName(fragName);
		if (f == null) {
			String fragmentStrType = e.getAttribute("type");
			int fragmentType;
			switch (fragmentStrType) {
			case "optional":
				fragmentType = Fragment.OPTIONAL;
				break;

			case "alternative":
				fragmentType = Fragment.ALTERNATIVE;
				break;

			case "parallel":
				fragmentType = Fragment.PARALLEL;
				break;

			case "loop":
				fragmentType = Fragment.LOOP;
				break;

			default:
				fragmentType = -1;
				break;
			}
			f = (Fragment) SequenceDiagramElement.createElement(
					SequenceDiagramElement.FRAGMENT, fragName);
			f.setType(fragmentType);
		}
		sd.addFragment(f);
	}


	private static void parseAllFragments(Document doc) {
		Element fragments = (Element) doc.getElementsByTagName("Fragments")
				.item(0);
		NodeList setOfFragments = fragments.getElementsByTagName("Fragment");
		for (int i = 0; i < setOfFragments.getLength(); i++) { // for each
																// fragment
																// found
			Element e = (Element) setOfFragments.item(i);
			String fragmentName = e.getAttribute("name");

			Fragment f = (Fragment) SequenceDiagramElement
					.getElementByName(fragmentName);

			NodeList setOfRepresentations = e
					.getElementsByTagName("RepresentedBy");
			for (int j = 0; j < setOfRepresentations.getLength(); j++) {
				Element r = (Element) setOfRepresentations.item(j);
				String seqDiagName = r.getAttribute("seqDiagName");

				SequenceDiagram sd = SequenceDiagram
						.getSequenceDiagramByName(seqDiagName);
				f.addSequenceDiagram(sd);
			}
		}
	}

	private static void parseAllLifelines(Document doc) {
		NodeList listOfLifelines = doc.getElementsByTagName("Lifeline");
		for (int i = 0; i < listOfLifelines.getLength(); i++) {
			Element lif = (Element) listOfLifelines.item(i);
			NamedNodeMap attributes = lif.getAttributes();
			String name = attributes.getNamedItem("name").getNodeValue();
			double reliability = Double.parseDouble(attributes.getNamedItem(
					"reliability").getNodeValue());

			Lifeline l = (Lifeline) SequenceDiagramElement.createElement(
					SequenceDiagramElement.LIFELINE, name);
			l.setReliability(reliability);
		}
	}

}
