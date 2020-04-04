package expressionsolver.functions;

import jadd.ADD;

import org.nfunk.jep.ParseException;


public class ADDSubtract extends org.nfunk.jep.function.Subtract {

    /* (non-Javadoc)
     * @see org.nfunk.jep.function.Subtract#sub(java.lang.Object, java.lang.Object)
     */
    @Override
    public Object sub(Object arg1, Object arg2) throws ParseException {
        if (arg1 instanceof ADD && arg2 instanceof ADD) {
            return ((ADD)arg1).minus((ADD)arg2);
        }
        throw new ParseException("Invalid parameter type");
    }

}
