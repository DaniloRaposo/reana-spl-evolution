package parsing.SplGeneratorModels;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import fdtmc.FDTMC;
import fdtmc.State;
import parsing.SplGeneratorModels.Activity;
import parsing.SplGeneratorModels.ActivityDiagram;
import parsing.SplGeneratorModels.ActivityDiagramElement;
import parsing.SplGeneratorModels.SequenceDiagram;
import parsing.SplGeneratorModels.Transition;
import parsing.SplGeneratorModels.SPLFilePersistence;
//import splGenerator.transformation.SequenceDiagramTransformer;
import tool.RDGNode;

public class Transformer {

	private HashMap<String, fdtmc.State> fdtmcStateById = new HashMap<String, fdtmc.State>();
	private RDGNode root;
	private HashMap<ActivityDiagramElement, State> stateByAdElement = new HashMap<ActivityDiagramElement, State>();

	/**
	 * This method is responsible for creating an RDG structure for a whole SPL
	 * given an activity diagram as input.
	 *
	 * @param ad
	 *            the activity diagram describing the coarse-grained behavior of
	 *            the SPL.
	 * @return the root node of the RDG structure built for the SPL.
	 */
	public RDGNode transformAD(ActivityDiagram ad) {
		FDTMC f = new FDTMC();
		f.setVariableName(ad.getName() + "_s");
		RDGNode answer = new RDGNode(ad.getName(), "true", f);
		root = answer;

		// Takes the first element (init) and transform it into its FDTMC
		// representation
		ActivityDiagramElement init = ad.getStartNode();
		transformAdElement(init, f);

		return answer;
	}

	private fdtmc.State transformAdElement(ActivityDiagramElement adElem,
			FDTMC f) {
		fdtmc.State answer = null;

		State isStateModeled = stateByAdElement.get(adElem);
		if (isStateModeled != null) {
			answer = isStateModeled;
			return answer;
		}

		fdtmc.State source = null;
		fdtmc.State isModeled;
		String adClass = adElem.getClass().getSimpleName();
		switch (adClass) {
		case "StartNode":
			source = f.createInitialState();
			f.createErrorState();
			stateByAdElement.put(adElem, source);

			HashSet<Activity> nextActivities = new HashSet<Activity>();
			for (Transition t : adElem.getTransitions()) {
				ActivityDiagramElement e = t.getTarget();
				Activity a;
				if (e instanceof Activity) {
					a = (Activity) e;
					nextActivities.add(a);
				}
			}

			for (Activity a : nextActivities) {
				fdtmc.State target = transformAdElement(a, f);
				f.createTransition(source, target, "", Double.toString(1.0));
				stateByAdElement.put(a, target);
			}
			source.setLabel(FDTMC.INITIAL_LABEL);
			answer = source;

			break;

		case "Activity":
			// 1st.: check if the activity is already modeled and its FDTMC is
			// available
			isModeled = fdtmcStateById.get(adElem.getElementName());
			if (isModeled == null) {
				// In case the activity was not modeled yet, we should model its
				// associated sequence diagrams
				Activity a = (Activity) adElem;
				source = f.createState();
				stateByAdElement.put(adElem, source);
				fdtmcStateById.put(adElem.getElementName(), source);
				// TODO Throw exception if there is more than one associated SD
				SequenceDiagram onlyAssociatedSD = a.getSequenceDiagrams().getFirst();
				SequenceDiagramTransformer sdt = new SequenceDiagramTransformer();
				RDGNode dependencyNode = sdt.transformSD(onlyAssociatedSD);
				this.root.addDependency(dependencyNode);

				// An activity should have only one transition (to another activity or to a decision node).
				ActivityDiagramElement nextElement = null;
				// TODO Throw exception if there is more than one outgoing transition.
				for (Transition t : adElem.getTransitions()) {
				    nextElement = t.getTarget();
				}
				fdtmc.State target = transformAdElement(nextElement, f);
				f.createInterface(dependencyNode.getId(), source, target, f.getErrorState());
				answer = source;
			} else
				answer = isModeled;
			break;

		case "EndNode":
			// 1st.: check if the end node is already modeled and its FDTMC is
			// available
			isModeled = fdtmcStateById.get(adElem.getElementName());
			if (isModeled == null) {
				source = f.createSuccessState();
				stateByAdElement.put(adElem, source);
				f.createTransition(source, source, "", Double.toString(1.0));
				answer = source;
			} else
				answer = isModeled;
			break;

		case "DecisionNode":
			// 1st.: check if the decision node is already modeled and its FDTMC
			// is already available
			isModeled = fdtmcStateById.get(adElem.getElementName());
			if (isModeled == null) {
				source = f.createState();
				stateByAdElement.put(adElem, source);
				for (Transition t : adElem.getTransitions()) {
					State target = transformAdElement(t.getTarget(), f);
					f.createTransition(source, target, t.getElementName(),
							Double.toString(t.getProbability()));
				}
				fdtmcStateById.put(adElem.getElementName(), source);
				answer = source;
			} else
				answer = isModeled;
			break;

		case "MergeNode":
			// 1st.: Check of the merge node is already modeled and its FDTMC is
			// already available
			isModeled = fdtmcStateById.get(adElem.getElementName());
			if (isModeled == null) {
				source = f.createState();
				stateByAdElement.put(adElem, source);
				for (Transition t : adElem.getTransitions()) {
					State target = transformAdElement(t.getTarget(), f);
					f.createTransition(source, target, "", Double.toString(1.0));
				}
				fdtmcStateById.put(adElem.getElementName(), source);
				answer = source;
			} else
				answer = isModeled;
			break;

		default:
			break;
		}

		return answer;
	}
}
