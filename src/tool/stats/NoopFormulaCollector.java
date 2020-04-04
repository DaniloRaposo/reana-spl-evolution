package tool.stats;

import java.io.PrintStream;

import tool.RDGNode;

public class NoopFormulaCollector implements IFormulaCollector {

    @Override
    public void collectFormula(RDGNode node, String formula) {
        // No-op
    }

    @Override
    public void printStats(PrintStream out) {
        // No-op
    }

}
