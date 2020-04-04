package expressionsolver.functions;

import jadd.ADD;

import org.nfunk.jep.ParseException;


public class UnaryMinus extends org.nfunk.jep.function.UMinus {

    /* (non-Javadoc)
     * @see org.nfunk.jep.function.UMinus#umin(java.lang.Object)
     */
    @Override
    public Object umin(Object arg0) throws ParseException {
        if (arg0 instanceof ADD) {
            return ((ADD)arg0).negate();
        }
        throw new ParseException("Invalid parameter type");
    }

}
