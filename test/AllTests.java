
import jadd.ADDConfigurationsTest;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import paramwrapper.FDTMCToParamTest;
import paramwrapper.ReliabilityFormulaTest;
import tool.AnalyzerTest;
import tool.RDGNodeTest;
import expressionsolver.ExpressionSolverTest;
import fdtmc.FDTMCTest;

@RunWith(Suite.class)
@SuiteClasses({
    FDTMCTest.class,
    FDTMCToParamTest.class,
    ReliabilityFormulaTest.class,
    ExpressionSolverTest.class,
    AnalyzerTest.class,
    RDGNodeTest.class,
    ADDConfigurationsTest.class
})
public class AllTests {

}
