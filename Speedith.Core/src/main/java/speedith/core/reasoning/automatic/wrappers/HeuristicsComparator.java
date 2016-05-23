package speedith.core.reasoning.automatic.wrappers;

import java.util.Comparator;

/**
 * Compares two proof attempts according to their heuristics.
 *
 * Note: this comparator imposes orderings that are inconsistent with equals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class HeuristicsComparator implements Comparator<ProofAttempt> {
    @Override
    public int compare(ProofAttempt p1, ProofAttempt p2) {
        return (p1.getCost()+p1.getHeuristic()) - (p2.getCost()+p2.getHeuristic());
    }
}
