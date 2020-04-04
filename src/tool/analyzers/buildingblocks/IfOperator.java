package tool.analyzers.buildingblocks;

/**
 * Functional if-then-else operator for booleans.
 *
 * @param <V> Value type
 */
public class IfOperator<V> implements IfThenElse<Boolean, V> {

    @Override
    public V apply(Boolean presence, V ifPresent, V ifAbsent) {
        if (presence) {
            return ifPresent;
        } else {
            return ifAbsent;
        }
    }

}
