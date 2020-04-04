package tool.analyzers;

import tool.RDGNode;
import jadd.ADD;

/**
 * NO-OP pruning strategy, i.e., do not prune invalid configurations at all.
 *
 * This strategy is useful for comparing analyses which do early pruning
 * of invalid configurations with ones which do late pruning (keep
 * reliability mappings small and see if the time gain pays itself).
 * @author thiago
 *
 */
public class NoPruningStrategy implements IPruningStrategy {

    @Override
    public ADD pruneInvalidConfigurations(RDGNode node, ADD reliability, ADD featureModel) {
        return reliability;
    }

}
