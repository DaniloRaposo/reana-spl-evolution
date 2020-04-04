package parsing.SplGeneratorModels;

import java.io.File;
import java.util.List;
import java.util.Map;

import parsing.activitydiagrams.ADReader;
import parsing.exceptions.InvalidNodeClassException;
import parsing.exceptions.InvalidNodeType;
import parsing.exceptions.InvalidNumberOfOperandsException;
import parsing.sequencediagrams.SDReader;
import tool.RDGNode;
import fdtmc.FDTMC;
import modeling.IModelerAPI;

public class SplGeneratorModelingAPI implements IModelerAPI {

	SPL spl; 
	
	public SplGeneratorModelingAPI() {
		// No-op
	}
	
	public SplGeneratorModelingAPI(File umlModels) {
		spl = SPL.getSplFromXml(umlModels.getAbsolutePath());
	}
	
	@Override
	public RDGNode transform() throws InvalidNumberOfOperandsException,
			InvalidNodeClassException, InvalidNodeType {
		Transformer t = new Transformer(); 
		RDGNode root = t.transformAD(spl.getActivityDiagram());
		return root;
	}

	@Override
	public void measureSizeModel(FDTMC fdtmc) {
		// TODO Auto-generated method stub

	}

	@Override
	public void printNumberOfCalls(String name) {
		// TODO Auto-generated method stub

	}

	@Override
	public Map<String, FDTMC> getFdtmcByName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SDReader> getSdParsers() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ADReader getAdParser() {
		// TODO Auto-generated method stub
		return null;
	}

}
