package tool.analyzers.buildingblocks;

import java.util.Map;

/**
 * Function for product derivation.
 *
 * @param <P> Presence type
 * @param <A> Asset type
 * @param <V> Value (derived) type
 */
@FunctionalInterface
public interface DerivationFunction<P, A, V> {

    V apply(P presence, A asset, Map<String, V> values);

    /**
     * Generates a derivation function based on an if-then-else operator,
     * an asset processing function to be executed for true-ish presences
     * and a default value to be used for false-ish presences.
     *
     * @param ite if-then-else operator
     * @param processAsset asset processor
     * @param defaultValue default value
     * @return
     */
    static <P, T, D> DerivationFunction<P, T, D> abstractDerivation(IfThenElse<P, D> ite,
                                                                    AssetProcessor<T, D> processAsset,
                                                                    D defaultValue) {
        return (presence, asset, values) -> ite.apply(presence,
                                                      processAsset.apply(asset, values),
                                                      defaultValue);
    }
}
