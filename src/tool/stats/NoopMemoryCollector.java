package tool.stats;

import java.io.PrintStream;

public class NoopMemoryCollector implements IMemoryCollector {

    @Override
    public void takeSnapshot(String name) {
        // No-op
    }

    @Override
    public void printStats(PrintStream out) {
        // No-op
    }

}
