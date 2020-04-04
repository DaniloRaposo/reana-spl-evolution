package paramwrapper;

import java.io.PrintStream;

public class NoopModelCollector implements IModelCollector {

    @Override
    public void collectModel(int variables, int states) {
        // NO-OP
    }

    @Override
    public void collectModelCheckingTime(long elapsedTime) {
        // NO-OP
    }

    @Override
    public void printStats(PrintStream out) {
        // NO-OP
    }

}
