/**
 *
 */
package expressionsolver.functions;

import jadd.ADD;

import org.nfunk.jep.ParseException;

/**
 * Add operator for ADDs.
 *
 * @author thiago
 *
 */
public class ADDAdd extends org.nfunk.jep.function.Add {

    @Override
    public Object add(Object param1, Object param2) throws ParseException {
        if (param1 instanceof ADD && param2 instanceof ADD) {
            return ((ADD)param1).plus((ADD)param2);
        }
        throw new ParseException("Invalid parameter type");
    }
}
