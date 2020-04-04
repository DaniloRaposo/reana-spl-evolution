package expressionsolver.functions;

import jadd.ADD;

import org.nfunk.jep.ParseException;


/**
 * @author thiago
 *
 */
public class ADDMultiply extends org.nfunk.jep.function.Multiply {

    /* (non-Javadoc)
     * @see org.nfunk.jep.function.Multiply#mul(java.lang.Object, java.lang.Object)
     */
    @Override
    public Object mul(Object arg1, Object arg2) throws ParseException {
        if (arg1 instanceof ADD && arg2 instanceof ADD) {
            return ((ADD)arg1).times((ADD)arg2);
        }
        throw new ParseException("Invalid parameter type");
    }

}
