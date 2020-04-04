package tool;

import jadd.JADD;
import jadd.UnrecognizedVariableException;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import tool.analyzers.IReliabilityAnalysisResults;
import expressionsolver.ExpressionSolver;

public class AnalyzerTest {
    private static final String PARAM_PATH = "/opt/param-2-3-64";

    String fmBSN = "Root  &&  (!Root  ||  Monitoring)  &&  (!Root  ||  Storage)  &&  (!Monitoring  ||  Root)  &&  (!Storage  ||  Root)  &&  (!Monitoring  ||  SensorInformation)  &&  (!Monitoring  ||  Sensor)  &&  (!SensorInformation  ||  Monitoring)  &&  (!Sensor  ||  Monitoring)  &&  (!SensorInformation  ||  Oxygenation  ||  PulseRate  ||  Temperature  ||  Position  ||  Fall)  &&  (!Oxygenation  ||  SensorInformation)  &&  (!PulseRate  ||  SensorInformation)  &&  (!Temperature  ||  SensorInformation)  &&  (!Position  ||  SensorInformation)  &&  (!Fall  ||  SensorInformation)  &&  (!Sensor  ||  SPO2  ||  ECG  ||  TEMP  ||  ACC)  &&  (!SPO2  ||  Sensor)  &&  (!ECG  ||  Sensor)  &&  (!TEMP  ||  Sensor)  &&  (!ACC  ||  Sensor)  &&  (!Storage  ||  SQLite  ||  Memory  ||  File)  &&  (!SQLite  ||  Storage)  &&  (!Memory  ||  Storage)  &&  (!File  ||  Storage)  &&  (!SQLite  ||  !Memory)  &&  (!SQLite  ||  !File)  &&  (!Memory  ||  !File)  &&  (!Oxygenation  ||  SPO2)  &&  (!PulseRate  ||  SPO2  ||  ECG)  &&  (!Fall  ||  ACC)  &&  (!Position  ||  ACC)  &&  (!Temperature  ||  TEMP)  &&  True  &&  !False  &&  (PulseRate  ||  ACC  ||  Memory  ||  Temperature  ||  Position  ||  Storage  ||  SensorInformation  ||  Sensor  ||  TEMP  ||  Monitoring  ||  Oxygenation  ||  File  ||  SQLite  ||  ECG  ||  Fall  ||  SPO2  ||  True)";
    JADD jadd;
    ExpressionSolver solver;
    Analyzer analyzer;

    @Before
    public void setUp() throws Exception {
        jadd = new JADD();
        solver = new ExpressionSolver(jadd);
        analyzer = new Analyzer(jadd, fmBSN, PARAM_PATH);
    }

    @Test
    public void testEvaluateReliabilitySQLite() throws CyclicRdgException, UnknownFeatureException {
        RDGNode sqlite = BSNNodes.getSQLiteRDGNode();
        IReliabilityAnalysisResults reliability = analyzer.evaluateFeatureFamilyBasedReliability(sqlite);

        String[] sqliteConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "SQLite"};
        Double expected = 0.998001;
        Assert.assertEquals(expected, reliability.getResult(sqliteConfig), 1E-14);
    }

    @Test
    public void testEvaluateReliabilityOxygenation() throws UnrecognizedVariableException, CyclicRdgException, UnknownFeatureException {
        RDGNode node = BSNNodes.getOxygenationRDGNode();
        IReliabilityAnalysisResults reliability = analyzer.evaluateFeatureFamilyBasedReliability(node);

        String[] sqliteConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "SQLite"};
        Assert.assertEquals("Configuration with SQLite",
                0.9920279440699441, reliability.getResult(sqliteConfig), 1E-14);

        String[] memoryConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "Memory"};
        Assert.assertEquals("Configuration with Memory",
                0.9920279440699441, reliability.getResult(memoryConfig), 1E-14);

        String[] fileConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "File"};
        Assert.assertEquals("Configuration without SQLite or Memory",
                0.994014980014994001, reliability.getResult(fileConfig), 1E-14);

        String[] noneConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2"};
        Assert.assertEquals("Invalid configuration",
                0, reliability.getResult(noneConfig), 1E-14);
    }


    @Test
    public void testEvaluateFeatureProductReliabilityOxygenation() throws UnrecognizedVariableException, CyclicRdgException, UnknownFeatureException {
        RDGNode node = BSNNodes.getOxygenationRDGNode();

        Set<Collection<String>> configurations = new HashSet<Collection<String>>();

        String[] sqliteConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "SQLite"};
        configurations.add(Arrays.asList(sqliteConfig));

        String[] memoryConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "Memory"};
        configurations.add(Arrays.asList(memoryConfig));

        String[] fileConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2",
                "File"};
        configurations.add(Arrays.asList(fileConfig));

        String[] noneConfig = new String[]{
                "Root",
                "Monitoring",
                "Storage",
                "SensorInformation",
                "Sensor",
                "Oxygenation",
                "SPO2"};
        configurations.add(Arrays.asList(noneConfig));

        IReliabilityAnalysisResults reliability = analyzer.evaluateFeatureProductBasedReliability(node, configurations.stream());
        Assert.assertEquals("Configuration with SQLite",
                0.9920279440699441, reliability.getResult(sqliteConfig), 1E-14);
        Assert.assertEquals("Configuration with Memory",
                0.9920279440699441, reliability.getResult(memoryConfig), 1E-14);
        Assert.assertEquals("Configuration without SQLite or Memory",
                0.994014980014994001, reliability.getResult(fileConfig), 1E-14);
    }

}
