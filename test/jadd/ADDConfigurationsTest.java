package jadd;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class ADDConfigurationsTest {

    @Before
    public void setUp() throws Exception {
    }

    @Test
    public void testConfigurationsWithoutDontCares() {
        String[] configArray = {"A", "B", "C"};
        List<String> config = Arrays.asList(configArray);
        Collection<List<String>> expanded = ADD.expandDontCares(config);

        Assert.assertEquals(1, expanded.size());
        Assert.assertTrue(expanded.contains(config));
    }

    @Test
    public void testConfigurationsWithDontCareAtStart() {
        String[] configArray = {"(A)", "B", "C"};
        List<String> config = Arrays.asList(configArray);
        Collection<List<String>> expanded = ADD.expandDontCares(config);

        Assert.assertEquals(2, expanded.size());
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "B", "C"})));
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"B", "C"})));
    }

    @Test
    public void testConfigurationsWithDontCareAtEnd() {
        String[] configArray = {"A", "B", "(C)"};
        List<String> config = Arrays.asList(configArray);
        Collection<List<String>> expanded = ADD.expandDontCares(config);

        Assert.assertEquals(2, expanded.size());
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "B", "C"})));
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "B"})));
    }

    @Test
    public void testConfigurationsWithDontCares() {
        String[] configArray = {"A", "(B)", "C", "(D)"};
        List<String> config = Arrays.asList(configArray);
        Collection<List<String>> expanded = ADD.expandDontCares(config);

        Assert.assertEquals(4, expanded.size());
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "B", "C", "D"})));
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "B", "C"})));
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "C", "D"})));
        Assert.assertTrue(expanded.contains(Arrays.asList(new String[]{"A", "C"})));
    }

}
