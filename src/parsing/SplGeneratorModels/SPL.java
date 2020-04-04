package parsing.SplGeneratorModels;

import java.io.StringWriter;
import java.io.File;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import javax.sound.midi.Sequence;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import parsing.SplGeneratorModels.ActivityDiagramParser;
import parsing.SplGeneratorModels.SequenceDiagramParser;
import splar.core.fm.FeatureModel;

public class SPL implements Cloneable{

	/**
	 * This attribute is redundant with SPLGenerator.modelsPath attribute. We
	 * should prune it soon.
	 */
	private String modelsPath = "/home/andlanna/workspace2/reana/src/splGenerator/generatedModels/";

	String name;
	FeatureModel fm;
	ActivityDiagram ad;
	ConfigurationKnowledge ck;


	private static SPL instance;

	public SPL(String name) {
		this();
		this.name = name;
	}

	public SPL() {
		this.ad = new ActivityDiagram();
	}

	/**
	 * This method is a factory method for instantiating a new SPL object
	 * containing its activity diagram.
	 * 
	 * @param name
	 *            - the parameter representing the name of the SPL.
	 * @return The SPL object created for the SPL.
	 */
	public static SPL createSPL(String name) {
		instance = new SPL(name);
		return instance;
	}

	public String getXmlRepresentation() {
		StringWriter answer = new StringWriter();
		File output = new java.io.File(new String(modelsPath + name
				+ "_behavioral_model.xml").replaceAll("\\s+", "_"));

		try {
			DocumentBuilderFactory docFactory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder docBuilder;

			docBuilder = docFactory.newDocumentBuilder();

			// CREATING THE XML STRUCTURE
			// root elements
			Document doc = docBuilder.newDocument();
			Element rootElement = doc.createElement("SplBehavioralModel");
			Attr splBehavioralModelName = doc.createAttribute("name");
			splBehavioralModelName.setValue(name);
			rootElement.setAttributeNode(splBehavioralModelName);
			doc.appendChild(rootElement);

			// Creating the DOM object representing the activity diagram
			Element domActDiagram = ad.getDOM(doc);
			rootElement.appendChild(domActDiagram);

			// Creating the DOM object representing the sequence diagrams
			List<Activity> setOfActivities = ad.getSetOfActivities();
			HashSet<SequenceDiagram> setOfSequenceDiagrams = new HashSet<SequenceDiagram>();
			HashSet<Lifeline> setOfLifelines = new HashSet<Lifeline>();
			HashSet<Fragment> setOfFragments = new HashSet<Fragment>();

			// 1st step --> get all the SequenceDiagrams, Lifelines and
			// Fragments used by the SPL.
			Iterator<Activity> ita = setOfActivities.iterator();
			while (ita.hasNext()) {
				Activity a = ita.next();
				// get all the sequence diagrams associated to the activity and
				// add them to the set of sequence diagrams.
//				System.out.println("----->");
				setOfSequenceDiagrams.addAll(a.getTransitiveSequenceDiagram());
//				System.out.println("=====>");
				setOfLifelines.addAll(a.getTransitiveLifelines());
				setOfFragments.addAll(a.getTransitiveFragments());
			}

			Iterator<SequenceDiagram> its = setOfSequenceDiagrams.iterator();

			Element domSeqDiagram = doc.createElement("SequenceDiagrams");
			its = setOfSequenceDiagrams.iterator();
			while (its.hasNext()) {
				SequenceDiagram d = its.next();
				Element e = d.getDOM(doc);
				domSeqDiagram.appendChild(e);
			}

			Element domLifelines = doc.createElement("Lifelines");
			Iterator<Lifeline> itl = setOfLifelines.iterator();
			while (itl.hasNext()) {
				Lifeline l = itl.next();
				Element domLife = doc.createElement("Lifeline");
				domLife.setAttribute("name", l.getName());
				domLife.setAttribute("reliability",
						Double.toString(l.getReliability()));
				domLifelines.appendChild(domLife);
			}

			Element domFragments = doc.createElement("Fragments");
			Iterator<Fragment> itf = setOfFragments.iterator();
			while (itf.hasNext()) {
				Fragment f = itf.next();
				Element domF = f.getDOM(doc);
				domFragments.appendChild(domF);
			}

			domSeqDiagram.appendChild(domLifelines);
			domSeqDiagram.appendChild(domFragments);
			rootElement.appendChild(domSeqDiagram);

			// Transform the content into an xml representation
			TransformerFactory transFactory = TransformerFactory.newInstance();
			Transformer transformer = transFactory.newTransformer();
			DOMSource source = new DOMSource(doc);
			StreamResult result = new StreamResult(answer);
			StreamResult result_file = new StreamResult(output);
			transformer.transform(source, result);
			transformer.transform(source, result_file);

		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return answer.toString();
	}

	public ActivityDiagram createActivityDiagram(String name) {
		ad = new ActivityDiagram();
		ad.setName(name);
		return ad;
	}

	public ActivityDiagram getActivityDiagram() {
		return ad;
	}

	/**
	 * This method's role is to read an XML file representing the behavioral
	 * models of a software product line, parse its document and create the
	 * models in memory.
	 * 
	 * @param fileName
	 *            the path of the file to be parsed
	 * @return the SPL object containing the behavioral models.
	 */
	public static SPL getSplFromXml(String fileName) {

		try {
			File xmlFile = new File(fileName);
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			Document doc = dBuilder.parse(xmlFile);

			// get the root element and extract the SPL name from it
			Element root = doc.getDocumentElement();
			Node nSplName = root.getAttributeNode("name");
			String splName = nSplName.getNodeValue();
			instance = new SPL(splName);

			// Call the parser of sequence diagrams elements initially, so it
			// allows to create in memory all the objects representing the SPL's
			// sequence diagrams.
			// Later, such objects will be linked to Activity Diagrams objects.
			SequenceDiagramParser.parse(doc);

			// build the activity diagram from the <ActivityDiagram> tag.
			NodeList nActivityDiagram = root
					.getElementsByTagName("ActivityDiagram");
			ActivityDiagram a = ActivityDiagramParser.parse(doc);
			instance.ad = a;

		} catch (Exception e) {
			e.printStackTrace();
		}

		return instance;
	}

	public String getName() {
		return name;
	}

	/**
	 * This method is used for defining the activity diagram describing the
	 * coarse-grained behavior of the software product line to the SPL object.
	 * 
	 * @param ad
	 *            - the activity diagram that will be assigned to the SPL
	 *            object.
	 */
	public void setActivityDiagram(ActivityDiagram ad) {
		this.ad = ad;
	}

	/**
	 * This method returns the FeatureModel object associated to the SPL.
	 * 
	 * @return the FeatureModel associated to the SPL.
	 */
	public FeatureModel getFeatureModel() {
		return fm;
	}

	/**
	 * This method is used for assigning a FeatureModel object to the SPL.
	 * 
	 * @param fm
	 */
	public void setFeatureModel(FeatureModel fm) {
		this.fm = fm;
	}
	
	public Object clone() throws CloneNotSupportedException {
		return super.clone();
	}

	public void setName(String name) {
		this.name = name;
	}

	public ConfigurationKnowledge getCk() {
		return ck;
	}

}
