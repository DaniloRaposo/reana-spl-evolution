package tool.analyzers.buildingblocks;

import java.util.Map;

/**
 * Interface for asset processing functions.
 *
 * This type of function assumes a mapping from component ids to actual values
 * to be used when processing.
 *
 * @param <A> Asset type
 * @param <V> Type of the values used during composition
 */
@FunctionalInterface
public interface AssetProcessor<A, V> {

    V apply(A asset, Map<String, V> values);

}
