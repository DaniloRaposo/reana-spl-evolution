package parsing;

public class ProbabilityEnergyTimeProfile {
    private float execTime;
    private float energy;
    private float prob;
    protected boolean hasProb = false;
    protected boolean hasExecTime = false;
    protected boolean hasEnergy = false;

    public float getEnergy() {
        return this.energy;
    }

    public float getExecTime() {
        return this.execTime;
    }

    public float getProbability() {
        return this.prob;
    }

    public boolean hasEnergy() {
        return this.hasEnergy;
    }

    public boolean hasExecTime() {
        return this.hasExecTime;
    }

    public boolean hasProbability() {
        return this.hasProb;
    }

    public void setProb(float prob) {
        this.hasProb = true;
        this.prob = prob;
    }

    public void setEnergy(float energy) {
        this.hasEnergy = true;
        this.energy = energy;
    }

    public void setExecTime(float execTime) {
        this.hasExecTime = true;
        this.execTime = execTime;
    }

}
