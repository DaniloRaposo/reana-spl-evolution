package tool.analyzers;

import tool.RDGNode;
import jadd.ADD;

/**
 * Pruning strategy which relies on multiplication of the reliability mappings
 * by the feature model's 0,1-ADD, so that valid configurations yield the same
 * reliability as before, but invalid ones yield 0.
 *
 * @author thiago
 *
 */
public class FeatureModelPruningStrategy implements IPruningStrategy {

    /* (non-Javadoc)
     * @see tool.IPruningStrategy#pruneInvalidConfigurations(tool.RDGNode, jadd.ADD, jadd.ADD)
     */
    @Override
    public ADD pruneInvalidConfigurations(RDGNode node, ADD reliability, ADD featureModel) {
        return featureModel.times(reliability);
    }

}
