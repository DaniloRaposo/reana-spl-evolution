package paramwrapper;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import fdtmc.FDTMC;
import fdtmc.State;
import paramwrapper.ParamWrapper;

public class ReliabilityFormulaTest {
    private static final String PARAM_PATH = "/opt/param-2-3-64";

	ParamWrapper paramWrapper;
	FDTMC fdtmc;

	@Before
	public void setUp() throws Exception {
		paramWrapper = new ParamWrapper(PARAM_PATH);
		fdtmc = new FDTMC();
		fdtmc.setVariableName("s");
	}

	@Test
	public void testReliabilityWithOneSuccessState() {
		State s0 = fdtmc.createState();
		State s1 = fdtmc.createState();
		State s2 = fdtmc.createState("success");
		State s3 = fdtmc.createState("error");
		fdtmc.createTransition(s0, s3, null, "1-r0");
		fdtmc.createTransition(s0, s1, null, "r0");
		fdtmc.createTransition(s1, s2, null, "1-rFail");
		fdtmc.createTransition(s1, s3, null, "rFail");
		fdtmc.createTransition(s2, s2, null, "1");
		fdtmc.createTransition(s3, s3, null, "1");

		String formula = paramWrapper.getReliability(fdtmc);
		assertEquals("-1*r0*rFail+1*r0", formula);
	}

	@Test
	public void testReliabilityWithTwoSuccessStates() {
		State s0 = fdtmc.createState();
		State s1 = fdtmc.createState("success");
		State s2 = fdtmc.createState("success");
		State s3 = fdtmc.createState("error");
		fdtmc.createTransition(s0, s3, null, "1-r0");
		fdtmc.createTransition(s0, s1, null, "r0");
		fdtmc.createTransition(s1, s2, null, "1-rFail");
		fdtmc.createTransition(s1, s3, null, "rFail");
		fdtmc.createTransition(s2, s2, null, "1");
		fdtmc.createTransition(s3, s3, null, "1");

		String formula = paramWrapper.getReliability(fdtmc);
		assertEquals("1*r0", formula);
	}

	@Test
	public void testReliabilityWithNoSuccessState() {
		State s0 = fdtmc.createState();
		State s1 = fdtmc.createState();
		State s2 = fdtmc.createState();
		State s3 = fdtmc.createState("error");
		fdtmc.createTransition(s0, s3, null, "1-r0");
		fdtmc.createTransition(s0, s1, null, "r0");
		fdtmc.createTransition(s1, s2, null, "1-rFail");
		fdtmc.createTransition(s1, s3, null, "rFail");
		fdtmc.createTransition(s2, s2, null, "1");
		fdtmc.createTransition(s3, s3, null, "1");

		String formula = paramWrapper.getReliability(fdtmc);
		assertEquals("0", formula);
	}

	@Test
	public void testReliabilityWithNoParameters() {
		State s0 = fdtmc.createState();
		State s1 = fdtmc.createState();
		State s2 = fdtmc.createState("success");
		State s3 = fdtmc.createState("error");
		fdtmc.createTransition(s0, s3, null, "0.01");
		fdtmc.createTransition(s0, s1, null, "0.99");
		fdtmc.createTransition(s1, s2, null, "0.99");
		fdtmc.createTransition(s1, s3, null, "0.01");
		fdtmc.createTransition(s2, s2, null, "1");
		fdtmc.createTransition(s3, s3, null, "1");

		String formula = paramWrapper.getReliability(fdtmc);
		assertEquals("(9801)/(10000)", formula);
	}
}
