package expressionsolver.functions;

import jadd.ADD;

import org.nfunk.jep.ParseException;


public class ADDDivide extends org.nfunk.jep.function.Divide {

    /* (non-Javadoc)
     * @see org.nfunk.jep.function.Divide#div(java.lang.Object, java.lang.Object)
     */
    @Override
    public Object div(Object arg1, Object arg2) throws ParseException {
        if (arg1 instanceof ADD && arg2 instanceof ADD) {
            return ((ADD)arg1).dividedBy((ADD)arg2);
        }
        throw new ParseException("Invalid parameter type");
    }

}
