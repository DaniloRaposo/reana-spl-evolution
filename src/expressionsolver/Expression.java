package expressionsolver;

import java.util.Map;
import java.util.logging.Logger;

import org.nfunk.jep.JEP;
import org.nfunk.jep.SymbolTable;

public class Expression<T> {
    private static final Logger LOGGER = Logger.getLogger(Expression.class.getName());

    private JEP parser;
    private Class<? extends T> type;

    /**
     * Creates a new Expression with the underlying {@code parser},
     * which operates on the given {@code type} (e.g., Double, ADD).
     * @param parser
     */
    public Expression(JEP parser, Class<? extends T> type) {
        this.parser = parser;
        this.type = type;
    }

    /**
     * Solves an expression with respect to the given interpretation of variables.
     * Here, variables are interpreted in the algebraic sense, not as boolean ADD-variables.
     * @param <T>
     *
     * @param expression
     * @param interpretation A map from variable names to the respective values
     *          to be considered during evaluation.
     * @return the result of applying the operations in the expression as defined
     *          for type {@code T}.
     */
    public T solve(Map<String, T> interpretation) {
        SymbolTable symbolTable = parser.getSymbolTable();
        for (Object var: symbolTable.keySet()) {
            String varName = (String)var;
            if (interpretation.containsKey(varName)) {
                parser.addVariableAsObject(varName, interpretation.get(varName));
            } else {
                LOGGER.warning("No interpretation for variable <"+varName+"> was provided");
            }
        }
        Object result = parser.getValueAsObject();
        return type.cast(result);
    }
}
