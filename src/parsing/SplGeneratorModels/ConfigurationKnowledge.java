package parsing.SplGeneratorModels;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import splar.core.fm.FeatureTreeNode;

public class ConfigurationKnowledge {

	private HashMap<Feature, LinkedList<SequenceDiagram>> mapping = new HashMap<Feature, LinkedList<SequenceDiagram>>();
	private HashMap<FeatureTreeNode, LinkedList<SequenceDiagram>> mappingSplar = new HashMap<FeatureTreeNode, LinkedList<SequenceDiagram>>();
	
	public void associateArtifact(Feature feature, SequenceDiagram artifact) {
		LinkedList<SequenceDiagram> list = mapping.get(feature); 
		if (list == null)
			list = new LinkedList<SequenceDiagram>();
		boolean sdInserted = list.add(artifact);
		if (sdInserted)
			feature.setAbstract(false);
		mapping.put(feature, list); 
	}


	public void associateArtifact(FeatureTreeNode feature, SequenceDiagram artifact) {
		LinkedList<SequenceDiagram> list = mappingSplar.get(feature); 
		if (list == null)
			list = new LinkedList<SequenceDiagram>();
		boolean sdInserted = list.add(artifact);
		if (sdInserted)
			feature.setProperty("abstract", "false");
		mappingSplar.put(feature, list);
	}
	
	/**
	 * This method returns a set of Features for which a sequence diagram has 
	 * an association in the configuration knowledge
	 * @param seqDiag the sequence diagram that we seek for associations in the
	 * configuration knowledge
	 * @return a list of features having association with the sequence diagram.
	 * In case there's no association in the configuration knowledge, null will
	 * be returned
	 */
	public HashSet<FeatureTreeNode> getAssociatedFeatures(SequenceDiagram seqDiag) {
		HashSet<FeatureTreeNode> answer = new HashSet<FeatureTreeNode>(); 
		
		Set<FeatureTreeNode> keys = mappingSplar.keySet();
		//looking for the sequence diagram in all keys entries
		for (FeatureTreeNode f : keys) {
			LinkedList<SequenceDiagram> values = mappingSplar.get(f);
			for (SequenceDiagram s : values) {
				if (s.equals(seqDiag))
					answer.add(f);
			}
		}
		
		if (answer.isEmpty())
			return null;
		
		return answer; 
	}
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		str.append("MAPPING: \n" ); 
		for (Feature f : mapping.keySet()) {
			str.append(f.getName() + ": ");
			for (SequenceDiagram s : mapping.get(f)) {
				str.append(s.getName() + " [" + s.getGuardCondition() + "], " ); 
				str.append("\n");
			}
		}
		str.append("\n\n");
		str.append("MAPPINGSPLAR: \n" ); 
		for (FeatureTreeNode f : mappingSplar.keySet()) {
			str.append(f.getName() + ": ");
			for (SequenceDiagram s : mappingSplar.get(f)) {
				str.append(s.getName() + " [" + s.getGuardCondition() + "], " ); 
				str.append("\n");
			}
		}
		return str.toString();
	}
}
