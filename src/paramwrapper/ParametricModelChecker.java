/**
 *
 */
package paramwrapper;

import fdtmc.FDTMC;

/**
 * Interface to a parametric model checker.
 * @author Thiago
 *
 */
public interface ParametricModelChecker {

	/**
	 * Evaluates the (parametric) reliability of an FDTMC.
	 * By convention, we assume that each success state is labeled
	 * with the string "success".
	 *
	 * @param fdtmc FDTMC to be evaluated.
	 * @return Formula parameterized on the transition probabilities.
	 */
	public String getReliability(FDTMC fdtmc);
}
