package tool.stats;

import java.io.PrintStream;

public interface IMemoryCollector {

    public void takeSnapshot(String name);

    public void printStats(PrintStream output);

}
