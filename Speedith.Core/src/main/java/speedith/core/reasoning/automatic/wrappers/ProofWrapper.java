package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.automatic.AutomaticProver;
import speedith.core.reasoning.rules.util.HeuristicUtils;

import java.util.Comparator;
import java.util.Set;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofWrapper implements Comparable{

    private Proof proof;

    private int cost;

    private int heuristic;

    public ProofWrapper(Proof proof) throws AutomaticProofException {
        this.proof = proof;
        if (proof == null) {
            throw new RuntimeException("Argument proof must not be null");
        }
        cost = proof.getRuleApplicationCount();
        heuristic = 0;
        for (SpiderDiagram goal : proof.getLastGoals().getGoals()) {
            if (AutomaticProver.isImplicationOfConjunctions(goal)) {
                CompoundSpiderDiagram impl = (CompoundSpiderDiagram) goal;
                heuristic += computeHeuristic(impl.getOperand(0), impl.getOperand(1));
            } else {
                throw new AutomaticProofException("The current goal is not an implication of conjunctions.");
            }
        }

    }

    public Proof getProof() {
        return proof;
    }

    @Override
    public int compareTo(Object o) {
        if (! (o instanceof ProofWrapper)) {
            throw  new RuntimeException("Object is not comparable with a ProofWrapper");
        }
        ProofWrapper other = (ProofWrapper) o;
        return (cost+getHeuristic()) - (other.getCost()+other.getHeuristic());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProofWrapper that = (ProofWrapper) o;

        return proof.equals(that.proof);

    }

    @Override
    public int hashCode() {
        return proof.hashCode();
    }

    public int getCost() {
        return cost;
    }

    public int getHeuristic() {
        return heuristic;
    }

    private int computeHeuristic(SpiderDiagram d1, SpiderDiagram d2) {
        return HeuristicUtils.contourDiffMetric(d1,d2)+
                HeuristicUtils.zoneDiffMetric(d1,d2) +
                notDiff(d1,d2)+
                Math.max(
                        HeuristicUtils.shadingDiffMetric(d1, d2),
                        HeuristicUtils.connectiveDiffMetric(d1, d2)
                );
    }

    private int connectiveDiff(SpiderDiagram d1, SpiderDiagram d2) {
        return 0;
    }

    private int shadingDiff(SpiderDiagram d1, SpiderDiagram d2) {
        return 0;
    }

    private int notDiff(SpiderDiagram d1, SpiderDiagram d2) {
        // TODO: negations are currently not considered (no proof rules for negations present)
        return 0;
    }

    private int zoneDiff(SpiderDiagram d1, SpiderDiagram d2) {
        return 0;
    }




}
