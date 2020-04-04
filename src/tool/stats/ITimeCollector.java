package tool.stats;

import java.io.PrintStream;

/**
 * Interface for a time stats collector for the ReAna tool.
 * @author thiago
 *
 */
public interface ITimeCollector {

    public void startTimer(String id);
    public void stopTimer(String id);
    /**
     * Wall-clock time accumulated during start-stop intervals.
     * @return
     */
    public long getCumulativeTime(String id);

    public void printStats(PrintStream out);

}
