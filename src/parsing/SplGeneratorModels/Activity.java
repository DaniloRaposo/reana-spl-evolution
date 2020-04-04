package parsing.SplGeneratorModels;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Activity extends ActivityDiagramElement {

	LinkedList<SequenceDiagram> sequenceDiagrams;

	public Activity() {
		super();
		sequenceDiagrams = new LinkedList<SequenceDiagram>();
	}

	public Activity(String elementName) {
		super(elementName);
		sequenceDiagrams = new LinkedList<SequenceDiagram>();
	}

	public boolean addSequenceDiagram(SequenceDiagram sd) {
		if (sequenceDiagrams == null)
			sequenceDiagrams = new LinkedList<SequenceDiagram>();

		boolean answer = sequenceDiagrams.add(sd);
		return answer;
	}

	public boolean containsSequenceDiagram(String seqDiagName) {
		Iterator<SequenceDiagram> itSeqDiag = sequenceDiagrams.iterator();
		SequenceDiagram s;
		while (itSeqDiag.hasNext()) {
			s = itSeqDiag.next();
			if (s.getName().equals(seqDiagName))
				return true;
		}
		return false;
	}

	public SequenceDiagram getSeqDiagByName(String seqDiagName) {
		Iterator<SequenceDiagram> itSeqDiag = sequenceDiagrams.iterator();
		SequenceDiagram s;

		while (itSeqDiag.hasNext()) {
			s = itSeqDiag.next();
			if (s.getName().equals(seqDiagName))
				return s;
		}
		return null;
	}

	public LinkedList<SequenceDiagram> getSequenceDiagrams() {
		return sequenceDiagrams;
	}

	public Element getDom(Document doc) {
		Element e = super.getDom(doc);

		if (sequenceDiagrams.size() > 0) {
			Iterator<SequenceDiagram> its = sequenceDiagrams.iterator();
			Element seqDiag;
			while (its.hasNext()) {
				SequenceDiagram sd = its.next();
				seqDiag = doc.createElement("RepresentedBy");
				seqDiag.setAttribute("seqDiagName", sd.getName());
				e.appendChild(seqDiag);
			}
		}

		return e;
	}

	/**
	 * This method implements a non-recursive version of the method for getting
	 * all sequence diagrams which can be reached from an activity.
	 * 
	 * @return a hashset containing all sequence diagrams gathered
	 */
	public HashSet<SequenceDiagram> getTransitiveSequenceDiagram() {
		HashSet<SequenceDiagram> answer = new HashSet<SequenceDiagram>();
		LinkedList<SequenceDiagram> pendingSDs = new LinkedList<SequenceDiagram>();
		LinkedList<Fragment> pendingFragments = new LinkedList<Fragment>();

		pendingSDs.addAll(getSequenceDiagrams());

		while (!pendingSDs.isEmpty()) {
			SequenceDiagram s = pendingSDs.removeFirst();
//			System.out.println("$$$$$$$$ "+s.getName() + " -> "+ s.getGuardCondition());
			pendingFragments.addAll(s.getFragments());
			for (Fragment fr : s.getFragments()) {
				if (!pendingFragments.contains(fr)) {
					pendingFragments.add(fr);
				}
			}
			answer.add(s);
			while (!pendingFragments.isEmpty()) {
				Fragment fr = pendingFragments.removeFirst();
//				System.out.println(">>> Fragment: " + fr.getName());
				for (SequenceDiagram sd : fr.getSequenceDiagrams()) {
					if (!pendingSDs.contains(sd)) {
//						System.out.println(">>>>>> Adicionando "+sd.getName() + " -> "+ sd.getGuardCondition());
						pendingSDs.add(sd);
					}
				}
			}
		}
		return answer;
	}

	/**
	 * This method implements a non-recursive version of the method for getting
	 * all lifelines enrolled at an activity's execution. All lifelines are
	 * returned by an HashSet.
	 * 
	 * @return a hashset containing all sequence diagrams gathered.
	 */
	public HashSet<Lifeline> getTransitiveLifelines() {
		HashSet<Lifeline> answer = new HashSet<Lifeline>();
		LinkedList<SequenceDiagram> pendingSDs = new LinkedList<SequenceDiagram>();
		LinkedList<Fragment> pendingFragments = new LinkedList<Fragment>();

		pendingSDs.addAll(getSequenceDiagrams());
		while (!pendingSDs.isEmpty()) {
			SequenceDiagram s = pendingSDs.removeFirst();
			answer.addAll(s.getLifelines());
			pendingFragments.addAll(s.getFragments());
			while (!pendingFragments.isEmpty()) {
				Fragment fr = pendingFragments.removeFirst();
				pendingSDs.addAll(fr.getSequenceDiagrams());
			}
		}
		return answer;
	}

	/**
	 * This method implements a non-recursive version of the method for getting
	 * all the fragments reachable from an activity, i.e., those fragments
	 * enrolled into activity's execution.
	 * 
	 * @return a hashset containing all fragments reachable from the activity
	 */
	public HashSet<Fragment> getTransitiveFragments() {
		HashSet<Fragment> answer = new HashSet<Fragment>();
		LinkedList<SequenceDiagram> pendingSDs = new LinkedList<SequenceDiagram>();
		LinkedList<Fragment> pendingFragments = new LinkedList<Fragment>();

		pendingSDs.addAll(getSequenceDiagrams());
		while (!pendingSDs.isEmpty()) {
			SequenceDiagram s = pendingSDs.removeFirst();
			pendingFragments.addAll(s.getFragments());
			while (!pendingFragments.isEmpty()) {
				Fragment fr = pendingFragments.removeFirst();
				answer.add(fr);
				pendingSDs.addAll(fr.getSequenceDiagrams());
			}
		}

		return answer;
	}
}
