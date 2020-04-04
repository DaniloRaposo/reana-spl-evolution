package tool;

import tool.analyzers.FeatureModelPruningStrategy;
import tool.analyzers.IPruningStrategy;
import tool.analyzers.NoPruningStrategy;

public class PruningStrategyFactory {

    private PruningStrategyFactory() {
        // NO-OP
    }

    public static IPruningStrategy createPruningStrategy(PruningStrategy strategySelection) {
        switch (strategySelection) {
        case NONE:
            return new NoPruningStrategy();
        case FM:
        default:
            return new FeatureModelPruningStrategy();
        }
    }

}
