package parsing.SplGeneratorModels;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import javax.swing.JOptionPane;

public class Feature {

	public static final boolean MANDATORY = true;
	public static final boolean ABSTRACT = true;
	public static final boolean HIDDEN = true;

	//Constants used to define the type of children's relation.
	public static final int LEAF = 0; 
	public static final int OR = 1; 
	public static final int AND = 2; 
	public static final int ALTERNATIVE = 3;
	
	//Set of features created for the Feature Model. 
	private static HashMap<String, Feature> features = 
			new HashMap<String, Feature>(); 
	
	
	private String name; 
	private LinkedList<Feature> children;
	private int type;
	private boolean mandatory;
	private boolean abs;
	private boolean hidden; 
	
	public static Feature createFeature(String name) {
		Feature f = new Feature(name); 
		features.put(name, f);
		if (features.get(name).equals(f))
			return f; 
		else 
			return null;
	}
	
	
	public Feature() {
		children = new LinkedList<Feature>();
	}
	
	public Feature(String name) {
		this();
		this.name = name;
	}

	public Feature addChild(String name, int type, boolean mand, boolean abs, 
			boolean hid) {
		Feature f = createFeature(name);
		
		f.setType(type);
		f.setMandatory(mand);
		f.setAbstract(abs);
		f.setHidden(hid);
		boolean inserted = children.add(f);
		if (inserted)
			return f; 
		else 
			return null;
	}




	private void setHidden(boolean hidden) {
		this.hidden = hidden; 
	}


	public void setAbstract(boolean abs) {
		this.abs = abs; 
	}


	void setMandatory(boolean mandatory) {
		this.mandatory = mandatory; 		
	}


	public LinkedList<Feature> getChildren() {
		return children;
	}


	public String getName() {
		return name;
	}

	
	public void setType(int type) {
		this.type = type;
	}

	
	public int getType() {
		return type;
	}


	public boolean isMandatory() {
		return mandatory;
	}


	public boolean isAbstract() {
		return abs;
	}


	public boolean isHidden() {
		return hidden;
	}


	public Feature getChildrenByName(String name) {
		Iterator<Feature> itFeat = children.iterator();
		Feature f; 
		while (itFeat.hasNext()) {
			f = itFeat.next(); 
			if (f.getName().equals(name))
				return f; 
		}
		return null;
	}


	public boolean deleteFeature(String name) {
		
		Feature f = features.get(name); 
		//1st step: delete the feature from the feature model
		boolean delFm = children.remove(f);
		
		//2nd step: delete the feature from the set of created features
		boolean delSetFeat = features.remove(f.getName(), f); 
		
		return (delFm && delSetFeat);
	}


	public void setName(String name) {
		this.name = name;		
	}


	public String exportXml() {
		StringBuilder featXml = new StringBuilder();
		String featInit, featBody = "", featEnd; 
		
		switch (this.type) {
		case Feature.LEAF:
			featInit = "<feature ";
			featInit += (abs ? "abstract=\"true\" " : "");
			featInit += (mandatory ? "mandatory=\"true\" " : "");
			featInit += "name=\""
					+ getName() + 
					"\" ";
			featEnd = "/>";
			break;

		default:
			featInit = "<"; 
			featInit += (this.type == Feature.AND ? "and " : "") + 
					(this.type == Feature.OR ? "or " : "") + 
					(this.type == Feature.ALTERNATIVE ? "alt " : ""); 
			featInit += (abs ? "abstract=\"true\" " : "");
			featInit += (mandatory ? "mandatory=\"true\" " : "");
			featInit += "name=\""
					+ getName() + 
					"\" ";
			featInit += ">";
			
			Iterator<Feature> it = children.iterator(); 
			while (it.hasNext()) {
				Feature f = it.next(); 
				featBody += f.exportXml();
			}
			
			featEnd = "</"
					+ (this.type == Feature.AND ? "and" : "")  
					+ (this.type == Feature.OR ? "or" : "")  
					+ (this.type == Feature.ALTERNATIVE ? "alt" : "") + 
					">";
			break;
		}
		
		featXml.append(featInit);
		featXml.append(featBody);
		featXml.append(featEnd);
		return featXml.toString();
	}


	

}
