package tool;

import tool.RDGNode;
import fdtmc.FDTMC;

/**
 * RDG nodes for the BSN.
 * @author thiago
 *
 */
public class BSNNodes {

    public static RDGNode getSQLiteRDGNode() {
        String id = "sqlite";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createSqliteFDTMC();
            node = new RDGNode(id, "SQLite", fdtmc);
        }
        return node;
    }

    public static RDGNode getFileRDGNode() {
        String id = "file";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createFileFDTMC();
            node = new RDGNode(id, "File", fdtmc);
        }
        return node;
    }

    public static RDGNode getMemoryRDGNode() {
        String id = "memory";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createMemoryFDTMC();
            node = new RDGNode(id, "Memory", fdtmc);
        }
        return node;
    }

    public static RDGNode getOxygenationRDGNode() {
        String id = "oxygenation";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createOxygenationFDTMC();
            node = new RDGNode(id, "Oxygenation", fdtmc);
            node.addDependency(getSQLiteRDGNode());
            node.addDependency(getFileRDGNode());
            node.addDependency(getMemoryRDGNode());
        }
        return node;
    }

    public static RDGNode getPulseRateRDGNode() {
        String id = "pulseRate";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createPulseRateFDTMC();
            node = new RDGNode(id, "PulseRate", fdtmc);
            node.addDependency(getSQLiteRDGNode());
            node.addDependency(getFileRDGNode());
            node.addDependency(getMemoryRDGNode());
        }
        return node;
    }

    public static RDGNode getSituationRDGNode() {
        String id = "situation";
        RDGNode node = RDGNode.getById(id);
        if (node == null) {
            FDTMC fdtmc = FDTMCStub.createSituationFDTMC();
            node = new RDGNode(id, "true", fdtmc);
            node.addDependency(getOxygenationRDGNode());
            node.addDependency(getPulseRateRDGNode());
        }
        return node;
    }

}
