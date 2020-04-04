package paramwrapper;

import java.io.PrintStream;

public interface IModelCollector {

    public void collectModel(int variables, int states);
    public void collectModelCheckingTime(long elapsedTimeNanos);
    public void printStats(PrintStream out);

}
