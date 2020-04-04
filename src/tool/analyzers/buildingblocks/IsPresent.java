package tool.analyzers.buildingblocks;

/**
 * Presence function for an asset.
 *
 * @param <A> Asset type
 * @param <P> Presence type (boolean-like)
 */
@FunctionalInterface
public interface IsPresent<A, P> {

    P apply(Component<A> component);

}
