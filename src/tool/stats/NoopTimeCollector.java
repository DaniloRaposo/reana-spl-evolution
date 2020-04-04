package tool.stats;

import java.io.PrintStream;

public class NoopTimeCollector implements ITimeCollector {

    @Override
    public void printStats(PrintStream out) {
        // No-op
    }

    @Override
    public void startTimer(String id) {
        // No-op
    }

    @Override
    public void stopTimer(String id) {
        // No-op
    }

    @Override
    public long getCumulativeTime(String id) {
        // No-op
        return 0;
    }

}
