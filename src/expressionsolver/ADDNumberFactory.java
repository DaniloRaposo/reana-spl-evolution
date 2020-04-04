/**
 *
 */
package expressionsolver;

import jadd.JADD;

import org.nfunk.jep.type.NumberFactory;

/**
 * NumberFactory which generates ADDs for constants.
 *
 * @author thiago
 *
 */
public class ADDNumberFactory implements NumberFactory {
    private JADD jadd;

    public ADDNumberFactory(JADD jadd) {
        this.jadd = jadd;
    }

    /* (non-Javadoc)
     * @see org.nfunk.jep.type.NumberFactory#createNumber(double)
     */
    @Override
    public Object createNumber(double constant) {
        return jadd.makeConstant(constant);
    }

}
