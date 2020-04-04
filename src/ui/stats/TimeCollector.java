package ui.stats;

import java.io.PrintStream;
import java.util.LinkedHashMap;
import java.util.Map;

import tool.stats.ITimeCollector;

public class TimeCollector implements ITimeCollector {

    private Map<String, WallClockStopWatch> timers;

    public TimeCollector() {
        // A LinkedHashMap preserves insertion order while iterating.
        timers = new LinkedHashMap<String, WallClockStopWatch>();
    }

    @Override
    public void startTimer(String id) {
        WallClockStopWatch timer = getTimer(id);
        timer.start();
    }

    @Override
    public void stopTimer(String id) {
        WallClockStopWatch timer = getTimer(id);
        timer.stop();
    }

    @Override
    public long getCumulativeTime(String id) {
        WallClockStopWatch timer = getTimer(id);
        return timer.getCumulativeTime();
    }

    @Override
    public void printStats(PrintStream out) {
        for (Map.Entry<String, WallClockStopWatch> entry: timers.entrySet()) {
            WallClockStopWatch timer = entry.getValue();
            out.println(entry.getKey() + ": " + timer.getCumulativeTime()/1E+6 + " ms");
        }
    }

    private WallClockStopWatch getTimer(String id) {
        if (timers.containsKey(id)) {
            return timers.get(id);
        } else {
            WallClockStopWatch timer = new WallClockStopWatch();
            timers.put(id, timer);
            return timer;
        }
    }

}
