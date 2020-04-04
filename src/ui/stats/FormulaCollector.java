package ui.stats;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import tool.RDGNode;
import tool.stats.IFormulaCollector;

public class FormulaCollector implements IFormulaCollector {

    private Map<RDGNode, String> formulae = new HashMap<RDGNode, String>();

    @Override
    public synchronized void collectFormula(RDGNode node, String formula) {
        formulae.put(node, formula);
    }

    @Override
    public void printStats(PrintStream out) {
        long count = 0;
        long minSize = Long.MAX_VALUE;
        long maxSize = 0;
        long sizesSum = 0;
        List<Integer> allFormulaeSizes = new LinkedList<Integer>();

        out.println("Formulae stats:");
        for (Map.Entry<RDGNode, String> entry: formulae.entrySet()) {
            RDGNode node = entry.getKey();
            int numChildren = node.getDependencies().size();
            int height = node.getHeight();
            String formula = entry.getValue();
            int formulaSize = formula.length();
            String formattedFormula = formulaSize < 1000 ?
                    "| " + formula
                    : "";
            out.println("    " + node + ": "
                        + numChildren + " children | height " + height + " | "
                        + formulaSize + " bytes " + formattedFormula);

            count++;
            minSize = Math.min(minSize, formulaSize);
            maxSize = Math.max(maxSize, formulaSize);
            sizesSum += formulaSize;
            allFormulaeSizes.add(formulaSize);
        }
        out.println("Maximum formula size: " + maxSize);
        out.println("Minimum formula size: " + minSize);
        out.println("Sum of formulae sizes: " + sizesSum);
        out.println("Number of formulae: " + count);
        out.println("All formulae sizes: " + allFormulaeSizes);
    }

}
