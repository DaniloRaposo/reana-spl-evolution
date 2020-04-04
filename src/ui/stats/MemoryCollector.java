package ui.stats;

import java.io.PrintStream;
import java.util.LinkedHashMap;
import java.util.Map;

import tool.stats.IMemoryCollector;

public class MemoryCollector implements IMemoryCollector {

    private Map<String, Long> snapshots;
    private long maxMemory = 0;

    public MemoryCollector() {
        // LinkedHashMap provides for ordered iteration of the snapshots.
        snapshots = new LinkedHashMap<String, Long>();
    }

    @Override
    public void takeSnapshot(String name) {
        Runtime runtime = Runtime.getRuntime();
        long snapshot = runtime.totalMemory() - runtime.freeMemory();
        snapshots.put(name, snapshot);
        maxMemory = Math.max(maxMemory, snapshot);
    }

    @Override
    public void printStats(PrintStream out) {
        for (Map.Entry<String, Long> snapshot: snapshots.entrySet()) {
            double valueInMegabytes = snapshot.getValue()/(1024.0*1024.0);
            out.println("Memory used "+snapshot.getKey()+": "+valueInMegabytes+" MB");
        }
        double maxMemoryInMegabytes = maxMemory/(1024.0*1024.0);
        out.println("Maximum memory used: "+maxMemoryInMegabytes+" MB");
    }

}
