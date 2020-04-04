package modeling;

import java.util.List;
import java.util.Map;

import parsing.activitydiagrams.ADReader;
import parsing.exceptions.InvalidNodeClassException;
import parsing.exceptions.InvalidNodeType;
import parsing.exceptions.InvalidNumberOfOperandsException;
import parsing.sequencediagrams.SDReader;
import tool.RDGNode;
import fdtmc.FDTMC;

public interface IModelerAPI {

	/**
	 * Triggers the applicable transformations, either AD or SD based
	 * @throws InvalidNumberOfOperandsException
	 * @throws InvalidNodeClassException
	 */
	public abstract RDGNode transform()
			throws InvalidNumberOfOperandsException, InvalidNodeClassException,
			InvalidNodeType;

	public abstract void measureSizeModel(FDTMC fdtmc);

	public abstract void printNumberOfCalls(String name);

	public abstract Map<String, FDTMC> getFdtmcByName();

	public abstract List<SDReader> getSdParsers();

	public abstract ADReader getAdParser();

}