package tool.analyzers.buildingblocks;

/**
 * Interface of an if-then-else operator.
 *
 * @param <P> Presence/condition type (boolean-like)
 * @param <V> Value type
 */
@FunctionalInterface
public interface IfThenElse<P, V> {

    V apply(P presence, V ifPresent, V ifAbsent);

}
