package parsing.sequencediagrams;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.DOMException;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import parsing.ProbabilityEnergyTimeProfile;
import parsing.ProbabilityEnergyTimeProfileReader;
import parsing.exceptions.InvalidTagException;
import parsing.exceptions.UnsupportedFragmentTypeException;

/**
 * Class responsible for parsing an MagicDraw designed fSD and
 * for populating the right information to the right objects.
 * Later, and SDReader instance will be consumed by an DiagramAPI instance
 */
public class SDReader {
    private static final Logger LOGGER = Logger.getLogger(SDReader.class.getName());

		private int index;
		private boolean next;
		private Map<Lifeline, List<String>> coverage;
		private Map<String, Lifeline> lifelinesByID;
		private Map<String, Message> messagesByID;
		private Document doc;
		private List<Lifeline> lifelines;
		private List<Message> messages;
		private Fragment sd;

	// Construtores

		public SDReader(File xmiFile, int index) {
			this.index = index;
			try {
				this.coverage = new HashMap<Lifeline, List<String>>();
				this.lifelinesByID = new HashMap<String, Lifeline>();
				this.messagesByID = new HashMap<String, Message>();
				this.lifelines = new ArrayList<Lifeline>();
				this.messages = new ArrayList<Message>();
				setDoc(xmiFile);
			} catch (Exception e) {
	            LOGGER.log(Level.SEVERE, e.toString(), e);
			}
		}

	// Public relevant methods

		/**
		 * Populates the SDReader.sd attribute from data obtained by
		 * 	retrieveLifelines() and retrieveMessages()
		 * @throws UnsupportedFragmentTypeException
		 * @throws InvalidTagException
		 * @throws DOMException
		 */
		public void traceDiagram() throws UnsupportedFragmentTypeException, InvalidTagException {
			NodeList nodes = this.doc.getElementsByTagName("ownedBehavior");
			this.next = (this.index == nodes.getLength() - 1) ? false : true;

			org.w3c.dom.Node n = nodes.item(this.index);
			NamedNodeMap nAttrs = n.getAttributes();
			retrieveLifelines(n);
			retrieveMessages(n);

			this.sd = new Fragment(
							extractId(nAttrs),
							extractName(nAttrs)
					  );

			this.sd.setLifelines(this.lifelines);

			NodeList nChilds = n.getChildNodes();
			for (int i = 0; i < nChilds.getLength(); i++) {

				org.w3c.dom.Node child = nChilds.item(i);
				if (child.getNodeName().equals("fragment")) {

					String xmiType = child.getAttributes().getNamedItem("xmi:type").getTextContent();
					if ("uml:MessageOccurrenceSpecification".equals(xmiType)) {

						String msgID = child.getAttributes().getNamedItem("message").getTextContent();
						this.sd.addNode(this.messagesByID.get(msgID));
						i += 2;

					} else if ("uml:CombinedFragment".equals(xmiType)) {

						NamedNodeMap cAttrs = child.getAttributes();
						Fragment newFragment =
								new Fragment(
										extractId(cAttrs),
										cAttrs.getNamedItem("interactionOperator").getTextContent(),
										extractName(cAttrs)
								);

						ProbabilityEnergyTimeProfile profile = ProbabilityEnergyTimeProfileReader.retrieveProbEnergyTime(newFragment.getId(), this.doc);
						newFragment.setProfile(profile);
						this.sd.addNode(newFragment);
						traceFragment(newFragment, child);

					}
				}
			}
		}

        private String extractId(NamedNodeMap nAttrs) {
            return nAttrs.getNamedItem("xmi:id").getTextContent();
        }

        private String extractName(NamedNodeMap nAttrs) {
            if (nAttrs.getNamedItem("name") != null) {
                return nAttrs.getNamedItem("name").getTextContent();
            } else {
                return "";
            }
        }

	// Private relevant methods

		/**
		 * Parses the xmi file in search for the SD respective Lifelines
		 * @throws InvalidTagException
		 * @throws UnsupportedFragmentTypeException
		 */
		private void retrieveLifelines(org.w3c.dom.Node node) throws InvalidTagException, UnsupportedFragmentTypeException {
			NodeList elements = node.getChildNodes();

			for (int s = 0; s < elements.getLength(); s++) {

				if (elements.item(s).getNodeName().equals("lifeline")) {
					NamedNodeMap sAttrs = elements.item(s).getAttributes();
					NodeList sChilds = elements.item(s).getChildNodes();
					Lifeline tmp = new Lifeline(extractId(sAttrs));
					List<String> coveredBy = new ArrayList<String>();

					tmp.setLink(sAttrs.getNamedItem("represents").getTextContent());
					if (sAttrs.getNamedItem("name") != null) {
						tmp.setName(sAttrs.getNamedItem("name").getTextContent());
					}

					for (int j = 0; j < sChilds.getLength(); j++) {
						if (sChilds.item(j).getNodeName().equals("coveredBy"))
							coveredBy.add(sChilds.item(j).getAttributes().getNamedItem("xmi:idref").getTextContent());
					}

					this.coverage.put(tmp, coveredBy);
					this.lifelines.add(tmp);
					this.lifelinesByID.put(tmp.getId(), tmp);
				}
			}

			for (int s = 0; s < elements.getLength(); s++) {
				if (elements.item(s).getNodeName().equals("ownedAttribute")) {
					for (int j = 0; j < this.lifelines.size(); j++) {
						if (this.lifelines.get(j).getLink().equals(
								elements.item(s).getAttributes().getNamedItem("xmi:id")
										.getTextContent())) {
							this.lifelines.get(j).setName(elements.item(s).getAttributes()
									.getNamedItem("name").getTextContent().replace('\n', ' '));
						}
					}
				}
			}
		}

		/**
		 * Parses the xmi file in search for the SD respective message exchanges
		 * @throws InvalidTagException
		 */
		private void retrieveMessages(org.w3c.dom.Node node) throws InvalidTagException {
			NodeList elements = node.getChildNodes();

			for (int s = 0; s < elements.getLength(); s++) {
				if ((elements.item(s).getNodeValue() == null) && (elements.item(s).getNodeName() == "message")) {
					NamedNodeMap sAttrs = elements.item(s).getAttributes();
					Message message = new Message(extractId(sAttrs));

					if (sAttrs.getNamedItem("name") != null) {
						message.setName(sAttrs.getNamedItem("name").getTextContent().replace("\n", " "));
					}

					for (Lifeline l: this.lifelines) {
						if (this.coverage.get(l).contains(sAttrs.getNamedItem("sendEvent").getTextContent())) {
							message.setSender(l);
						}
						if (this.coverage.get(l).contains(sAttrs.getNamedItem("receiveEvent").getTextContent())) {
							message.setReceiver(l);
						}
					}

					if (sAttrs.getNamedItem("messageSort") != null) {
					    String messageSortContent = sAttrs.getNamedItem("messageSort").getTextContent();
						if ("asynchCall".equals(messageSortContent) || "asynchSignal".equals(messageSortContent)) {
							message.setType(MessageType.ASYNCHRONOUS);
						} else if ("reply".equals(messageSortContent)) {
							message.setType(MessageType.REPLY);
						}
					} else {
						message.setType(MessageType.SYNCHRONOUS);
					}

					ProbabilityEnergyTimeProfile profile = ProbabilityEnergyTimeProfileReader.retrieveProbEnergyTime(message.getId(), this.doc);
					message.setProfile(profile);
					this.messages.add(message);
					this.messagesByID.put(message.getId(), message);
				}
			}
		}

		/**
		 * Populates an operand structure
		 * @param operand
		 * @param node
		 * @throws UnsupportedFragmentTypeException
		 * @throws DOMException
		 * @throws InvalidTagException
		 */
		private void traceOperand(Operand operand, org.w3c.dom.Node node) throws UnsupportedFragmentTypeException, InvalidTagException {
			NodeList oChilds = node.getChildNodes();

			for (int k = 0; k < oChilds.getLength(); k++) {

				org.w3c.dom.Node itemK = oChilds.item(k);
                if ("fragment".equals(itemK.getNodeName())) {

					NamedNodeMap kAttrs = itemK.getAttributes();
					String typeContent = kAttrs.getNamedItem("xmi:type").getTextContent();
					if ("uml:MessageOccurrenceSpecification".equals(typeContent)) {

						String msgID = kAttrs.getNamedItem("message").getTextContent();
						operand.addNode(this.messagesByID.get(msgID));
						k+=2;

					} else if ("uml:CombinedFragment".equals(typeContent)) {

						Fragment innerFragment =
									new Fragment(
										extractId(kAttrs),
										kAttrs.getNamedItem("interactionOperator").getTextContent(),
										extractName(kAttrs)
									);

						ProbabilityEnergyTimeProfile profile = ProbabilityEnergyTimeProfileReader.retrieveProbEnergyTime(innerFragment.getId(), this.doc);
                        innerFragment.setProfile(profile);
						operand.addNode(innerFragment);
						traceFragment(innerFragment, itemK);
					}

				} else if ("guard".equals(itemK.getNodeName())) {
					NodeList kChilds = itemK.getChildNodes();
					for (int l = 0; l < kChilds.getLength(); l++) {
					    org.w3c.dom.Node itemL = kChilds.item(l);
						if ("specification".equals(itemL.getNodeName())) {
							operand.setGuard(itemL.getAttributes()
									.getNamedItem("value").getTextContent());

							break;
						}
					}
				}
			}
		}

		/**
		 * Populates an fragment structure
		 * @param fragment
		 * @param node
		 * @throws UnsupportedFragmentTypeException
		 * @throws InvalidTagException
		 * @throws DOMException
		 */
		private void traceFragment(Fragment fragment, org.w3c.dom.Node node) throws UnsupportedFragmentTypeException, InvalidTagException {
			NodeList fChilds = node.getChildNodes();

			for (int j = 0; j < fChilds.getLength(); j++) {
				NamedNodeMap jAttrs = fChilds.item(j).getAttributes();
				org.w3c.dom.Node item = fChilds.item(j);
				if ("covered".equals(item.getNodeName())) {
					fragment.addLifeline(this.lifelinesByID.get(jAttrs.getNamedItem("xmi:idref").getTextContent()));
				} else if ("operand".equals(item.getNodeName())) {
					Operand newOperand = new Operand(extractId(jAttrs));
					traceOperand(newOperand, item);
					fragment.addNode(newOperand);
				}

			}
		}


	// Getters and Setters

		public int getIndex() {
			return index;
		}

		public void setIndex(int index) {
			this.index = index;
		}

		public boolean hasNext() {
			return next;
		}

		public void setNext(boolean next) {
			this.next = next;
		}

		public Map<Lifeline, List<String>> getCoverage() {
			return coverage;
		}

		public void setCoverage(Map<Lifeline, List<String>> coverage) {
			this.coverage = coverage;
		}

		public Map<String, Lifeline> getLifelinesByID() {
			return lifelinesByID;
		}

		public void setLifelinesByID(Map<String, Lifeline> lifelinesByID) {
			this.lifelinesByID = lifelinesByID;
		}

		public Map<String, Message> getMessagesByID() {
			return messagesByID;
		}

		public void setMessagesByID(Map<String, Message> messagesByID) {
			this.messagesByID = messagesByID;
		}

		public Document getDoc() {
			return doc;
		}

		public void setDoc(Document doc) {
			this.doc = doc;
		}

		public void setDoc(File xmiFile) throws ParserConfigurationException, SAXException, IOException {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			this.doc = db.parse(xmiFile);
			this.doc.getDocumentElement().normalize();
		}

		public List<Lifeline> getLifelines() {
			return lifelines;
		}

		public void setLifelines(List<Lifeline> lifelines) {
			this.lifelines = lifelines;
		}

		public List<Message> getMessages() {
			return messages;
		}

		public void setMessages(List<Message> messages) {
			this.messages = messages;
		}

		public Fragment getSD() {
			return sd;
		}

		public void setSD(Fragment sd) {
			this.sd = sd;
		}
}
