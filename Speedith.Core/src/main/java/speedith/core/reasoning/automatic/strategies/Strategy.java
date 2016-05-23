package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;

/**
 * A strategy for computing the cost and heuristic function for the proof.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface Strategy {


    /**
     * Computes, how much the proof has cost to produce.
     * @param p A proof
     * @return the cost of p
     */
    int getCost(Proof p);

    /**
     * Computes the heuristic function for the given proof, i.e., how "far" it is from the goal
     * @param p a proof
     * @return the heuristic of p
     * @throws AutomaticProofException if a subgoal of the proof is not an implication of conjunctions
     */
    int getHeuristic(Proof p) throws AutomaticProofException;
}
