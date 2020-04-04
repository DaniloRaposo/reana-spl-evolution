package tool;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import tool.analyzers.buildingblocks.Component;
import fdtmc.FDTMC;


public class RDGNode {

	//This reference is used to store all the RDGnodes created during the evaluation
	private static Map<String, RDGNode> rdgNodes = new HashMap<String, RDGNode>();
	private static List<RDGNode> nodesInCreationOrder = new LinkedList<RDGNode>();

    private static int lastNodeIndex = 0;

	// Node identifier
	private String id;
	//This attribute is used to store the FDTMC for the RDG node.
	private FDTMC fdtmc;
	/**
	 * The node must have an associated presence condition, which is
	 * a boolean expression over features.
	 */
	private String presenceCondition;
	// Nodes on which this one depends
	private Collection<RDGNode> dependencies;
	/**
	 * Height of the RDGNode.
	 */
	private int height;


	/**
	 * The id, presence condition and model (FDTMC) of an RDG node must
	 * be immutable, so there must be no setters for them. Hence, they
	 * must be set at construction-time.
	 *
	 * @param id Node's identifier. It is preferably a valid Java identifier.
	 * @param presenceCondition Boolean expression over features (using Java operators).
	 * @param fdtmc Stochastic model of the piece of behavioral model represented by
	 *             this node.
	 */
	public RDGNode(String id, String presenceCondition, FDTMC fdtmc) {
	    this.id = id;
	    this.presenceCondition = presenceCondition;
	    this.fdtmc = fdtmc;
		this.dependencies = new HashSet<RDGNode>();
		this.height = 0;

		rdgNodes.put(id, this);
		nodesInCreationOrder.add(this);
	}

    public FDTMC getFDTMC() {
        return this.fdtmc;
    }

    public void addDependency(RDGNode child) {
        this.dependencies.add(child);
        height = Math.max(height, child.height + 1);
    }

    public Collection<RDGNode> getDependencies() {
        return dependencies;
    }

    public String getPresenceCondition() {
        return presenceCondition;
    }

    public String getId() {
        return id;
    }

    /**
     * Height of the RDGNode. This metric is defined in the same way as
     * the height of a tree node, i.e., the maximum number of nodes in a path
     * from this one to a leaf (node with no dependencies).
     */
    public int getHeight() {
        return height;
    }

    public static RDGNode getById(String id) {
        return rdgNodes.get(id);
    }

    public static String getNextId() {
        return "n" + lastNodeIndex++;
    }

    /**
     * We consider two RDG nodes to be equal whenever their behavior is
     * modeled by equal FDTMCs, their presence condition is the same and
     * their dependencies are also correspondingly equal.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof RDGNode) {
            RDGNode other = (RDGNode) obj;
            return this.getPresenceCondition().equals(other.getPresenceCondition())
                    && this.getFDTMC().equals(other.getFDTMC())
                    && this.getDependencies().equals(other.getDependencies());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return id.hashCode() + presenceCondition.hashCode() + fdtmc.hashCode() + dependencies.hashCode();
    }

    @Override
    public String toString() {
        return getId() + " (" + getPresenceCondition() + ")";
    }

    /**
     * Retrieves the transitive closure of the RDGNode dependency relation.
     * The node itself is part of the returned list.
     *
     * It implements the Cormen et al.'s topological sort algorithm.
     *
     * @return The descendant RDG nodes ordered bottom-up (depended-upon to dependent).
     * @throws CyclicRdgException if there is a path with a cycle starting from this node.
     */
    public List<RDGNode> getDependenciesTransitiveClosure() throws CyclicRdgException {
        List<RDGNode> transitiveDependencies = new LinkedList<RDGNode>();
        Map<RDGNode, Boolean> marks = new HashMap<RDGNode, Boolean>();
        topoSortVisit(this, marks, transitiveDependencies);
        return transitiveDependencies;
    }

    /**
     * Topological sort {@code visit} function (Cormen et al.'s algorithm).
     * @param node
     * @param marks
     * @param sorted
     * @throws CyclicRdgException
     */
    private void topoSortVisit(RDGNode node, Map<RDGNode, Boolean> marks, List<RDGNode> sorted) throws CyclicRdgException {
        if (marks.containsKey(node) && marks.get(node) == false) {
            // Visiting temporarily marked node -- this means a cyclic dependency!
            throw new CyclicRdgException();
        } else if (!marks.containsKey(node)) {
            // Mark node temporarily (cycle detection)
            marks.put(node, false);
            for (RDGNode child: node.getDependencies()) {
                topoSortVisit(child, marks, sorted);
            }
            // Mark node permanently (finished sorting branch)
            marks.put(node, true);
            sorted.add(node);
        }
    }

    /**
     * Computes the number of paths from source nodes to every known node.
     * @return A map associating an RDGNode to the corresponding number
     *      of paths from a source node which lead to it.
     * @throws CyclicRdgException
     */
    public Map<RDGNode, Integer> getNumberOfPaths() throws CyclicRdgException {
        Map<RDGNode, Integer> numberOfPaths = new HashMap<RDGNode, Integer>();

        Map<RDGNode, Boolean> marks = new HashMap<RDGNode, Boolean>();
        Map<RDGNode, Map<RDGNode, Integer>> cache = new HashMap<RDGNode, Map<RDGNode,Integer>>();
        Map<RDGNode, Integer> tmpNumberOfPaths = numPathsVisit(this, marks, cache);
        numberOfPaths = sumPaths(numberOfPaths, tmpNumberOfPaths);

        return numberOfPaths;
    }

    // TODO Parameterize topological sort of RDG.
    private static Map<RDGNode, Integer> numPathsVisit(RDGNode node, Map<RDGNode, Boolean> marks, Map<RDGNode, Map<RDGNode, Integer>> cache) throws CyclicRdgException {
        if (marks.containsKey(node) && marks.get(node) == false) {
            // Visiting temporarily marked node -- this means a cyclic dependency!
            throw new CyclicRdgException();
        } else if (!marks.containsKey(node)) {
            // Mark node temporarily (cycle detection)
            marks.put(node, false);

            Map<RDGNode, Integer> numberOfPaths = new HashMap<RDGNode, Integer>();
            // A node always has a path to itself.
            numberOfPaths.put(node, 1);
            // The number of paths from a node X to a node Y is equal to the
            // sum of the numbers of paths from each of its descendants to Y.
            for (RDGNode child: node.getDependencies()) {
                Map<RDGNode, Integer> tmpNumberOfPaths = numPathsVisit(child, marks, cache);
                numberOfPaths = sumPaths(numberOfPaths, tmpNumberOfPaths);
            }
            // Mark node permanently (finished sorting branch)
            marks.put(node, true);
            cache.put(node, numberOfPaths);
            return numberOfPaths;
        }
        // Otherwise, the node has already been visited.
        return cache.get(node);
    }

    /**
     * Sums two paths-counting maps
     * @param pathsCountA
     * @param pathsCountB
     * @return
     */
    private static Map<RDGNode, Integer> sumPaths(Map<RDGNode, Integer> pathsCountA, Map<RDGNode, Integer> pathsCountB) {
        Map<RDGNode, Integer> numberOfPaths = new HashMap<RDGNode, Integer>(pathsCountA);
        for (Map.Entry<RDGNode, Integer> entry: pathsCountB.entrySet()) {
            RDGNode node = entry.getKey();
            Integer count = entry.getValue();
            if (numberOfPaths.containsKey(node)) {
                count += numberOfPaths.get(node);
            }
            numberOfPaths.put(node, count);
        }
        return numberOfPaths;
    }

    /**
     * Returns the first RDG node (in crescent order of creation time) which is similar
     * to the one provided.
     *
     * A similar RDG node is one for which equals() returns true.
     * @param rdgNode
     * @return a similar RDG node or null in case there is none.
     */
    public static RDGNode getSimilarNode(RDGNode target) {
        for (RDGNode candidate: nodesInCreationOrder) {
            if (candidate != target && candidate.equals(target)) {
                return candidate;
            }
        }
        return null;
    }

    /**
     * Converts this RDG node into a Component<FDTMC>.
     * @return
     */
    public Component<FDTMC> toComponent() {
        Collection<Component<FDTMC>> dependencies = this.getDependencies().stream()
                .map(RDGNode::toComponent)
                .collect(Collectors.toSet());
        return new Component<FDTMC>(this.getId(),
                                    this.getPresenceCondition(),
                                    this.getFDTMC(),
                                    dependencies);
    }

    public static List<Component<FDTMC>> toComponentList(List<RDGNode> nodes) {
        return nodes.stream()
                .map(RDGNode::toComponent)
                .collect(Collectors.toList());
    }

}
