package speedith.core.reasoning.automatic.wrappers;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.automatic.strategies.Strategy;


/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofAttempt implements Comparable<ProofAttempt>{

    private Proof proof;

    private int cost;

    private int heuristic;

    public ProofAttempt(Proof proof, Strategy strategy) throws AutomaticProofException {
        this.proof = proof;
        if (proof == null) {
            throw new RuntimeException("Argument proof must not be null");
        }
        cost = strategy.getCost(proof);
        heuristic = strategy.getHeuristic(proof);
    }

    public Proof getProof() {
        return proof;
    }

    @Override
    public int compareTo(ProofAttempt o) {
        return (cost+getHeuristic()) - (o.getCost()+o.getHeuristic());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProofAttempt that = (ProofAttempt) o;

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

//    private int computeHeuristic(SpiderDiagram d1, SpiderDiagram d2) {
//        return HeuristicUtils.metric(d1,d2);
//    }

}