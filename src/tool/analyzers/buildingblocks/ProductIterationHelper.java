package tool.analyzers.buildingblocks;

import java.util.Collection;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class ProductIterationHelper {

    public static <T> Map<Collection<String>, Double> evaluate(Function<Collection<String>, Double> eval,
                                                               Stream<Collection<String>> configurations,
                                                               ConcurrencyStrategy concurrencyStrategy) {
        Stream<Collection<String>> configs = concurrencyStrategy == ConcurrencyStrategy.PARALLEL ?
                                                        configurations.parallel()
                                                        : configurations.sequential();

        Map<Collection<String>, Double> results = configs
                .collect(Collectors.toMap(Function.identity(),
                                          eval));
        return results;
    }

}
