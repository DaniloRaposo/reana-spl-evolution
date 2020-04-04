package tool.stats;

import java.io.PrintStream;

import tool.RDGNode;

/**
 * Collects formulas in order to generate stats.
 * @author thiago
 *
 */
public interface IFormulaCollector {

    public void collectFormula(RDGNode node, String formula);

    public void printStats(PrintStream out);

}
