package tool.analyzers;

import tool.RDGNode;
import jadd.ADD;

/**
 * Interface for invalid configurations pruning strategies.
 * @author thiago
 *
 */
public interface IPruningStrategy {

    /**
     * Given an RDG node and its reliability mapping, uses feature model
     * information in order to prune partial configurations which can be
     * proven invalid in the global context.
     *
     * @param node An RDG node.
     * @param reliability Reliability mapping for {@code node.}
     * @param featureModel 0,1-ADD representing the valid configurations for the SPL.
     * @return ADD with a reliability mapping for {@code node} in which the
     *  reliability of invalid partial configurations is represented by zero.
     */
    public ADD pruneInvalidConfigurations(RDGNode node, ADD reliability, ADD featureModel);

}
