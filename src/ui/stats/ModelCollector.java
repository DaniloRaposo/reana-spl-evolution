package ui.stats;

import java.io.PrintStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import paramwrapper.IModelCollector;

public class ModelCollector implements IModelCollector {
    private class Model {
        int variables;
        int states;
    }

    private List<Model> models = Collections.synchronizedList(new LinkedList<Model>());
    private List<Double> times = Collections.synchronizedList(new LinkedList<Double>());

    @Override
    public void collectModel(int variables, int states) {
        Model model = new Model();
        model.variables = variables;
        model.states = states;
        models.add(model);
    }

    @Override
    public void collectModelCheckingTime(long elapsedTimeNanos) {
        times.add(elapsedTimeNanos/1E+6);
    }

    @Override
    public void printStats(PrintStream out) {
        int maxVars = 0;
        int minVars = Integer.MAX_VALUE;
        int maxStates = 0;
        int minStates = Integer.MAX_VALUE;
        int statesSum = 0;
        int count = 0;

        out.println("Models stats:");
        synchronized (models) {
            for (Model model: models) {
                int variables = model.variables;
                int states = model.states;

                out.println("    states: " + states + " | vars: " + variables);

                count++;
                minVars = Math.min(minVars, variables);
                maxVars = Math.max(maxVars, variables);
                minStates = Math.min(minStates, states);
                maxStates = Math.max(maxStates, states);
                statesSum += states;
            }
        }

        out.println("Maximum vars in a model: " + maxVars);
        out.println("Minimum vars in a model: " + minVars);
        out.println("Maximum states in a model: " + maxStates);
        out.println("Minimum states in a model: " + minStates);
        out.println("Sum of models' states: " + statesSum);
        out.println("Number of models: " + count);

        synchronized (times) {
            out.println("All model checking times (ms): " + times);
        }
    }

}
