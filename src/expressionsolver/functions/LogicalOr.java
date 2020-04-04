package expressionsolver.functions;

import jadd.ADD;

import java.util.Stack;

import org.nfunk.jep.ParseException;
import org.nfunk.jep.function.PostfixMathCommand;

public class LogicalOr extends PostfixMathCommand {

    public LogicalOr() {
        numberOfParameters = 2;
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    @Override
    public void run(Stack inStack) throws ParseException {
        checkStack(inStack);// check the stack

        Object param2 = inStack.pop();
        Object param1 = inStack.pop();

        if ((param1 instanceof ADD) && (param2 instanceof ADD)) {
            ADD result = ((ADD) param1).or((ADD) param2);
            inStack.push(result); // push the result on the inStack
            return;
        }
        throw new ParseException("Invalid parameter type");
    }
}
