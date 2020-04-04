package expressionsolver.functions;

import jadd.ADD;
import jadd.JADD;
import jadd.UnrecognizedVariableException;

import org.nfunk.jep.ParseException;


/**
 * @author thiago
 *
 */
public class ADDPower extends org.nfunk.jep.function.Power {

    private JADD jadd;

    public ADDPower(JADD jadd) {
        this.jadd = jadd;
    }

    /* (non-Javadoc)
     * @see org.nfunk.jep.function.Power#power(java.lang.Object, java.lang.Object)
     */
    @Override
    public Object power(Object arg1, Object arg2) throws ParseException {
        if (arg1 instanceof ADD && arg2 instanceof ADD) {
            ADD base = (ADD)arg1;
            ADD exponent = (ADD)arg2;
            if (!exponent.isConstant()) {
                throw new ParseException("Invalid parameter type. Exponent must be constant.");
            }

            double exponentValue = 0;
            try {
                exponentValue = exponent.eval(new String[]{});
            } catch (UnrecognizedVariableException e) {
                // Unreachable
            }

            return nTimes(base, Math.round(exponentValue));
        }
        throw new ParseException("Invalid parameter type");
    }

    private ADD nTimes(ADD base, long exponentValue) {
        if (exponentValue == 0) {
            return base.ifThenElse(jadd.makeConstant(1),
                                   jadd.makeConstant(0));
        }
        ADD result = base;
        for (int i = 1; i < exponentValue; i++) {
            result = result.times(base);
        }
        return result;
    }

}
