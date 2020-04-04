package tool;

public class UnknownFeatureException extends RuntimeException {

    private static final long serialVersionUID = 1851586698842170238L;
    private final String featureName;

    public UnknownFeatureException(String featureName) {
        super("Unrecognized feature: " + featureName);
        this.featureName = featureName;
    }

    public String getFeatureName() {
        return featureName;
    }

}
