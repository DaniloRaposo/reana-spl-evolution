package ui.stats;

public class WallClockStopWatch {

    private long startTime;
    private long cumulativeTime = 0;

    public void start() {
        startTime = System.nanoTime();
    }

    public long stop() {
        long delta = System.nanoTime() - startTime;
        cumulativeTime += delta;
        return delta;
    }

    public long getCumulativeTime() {
        return cumulativeTime;
    }
}
