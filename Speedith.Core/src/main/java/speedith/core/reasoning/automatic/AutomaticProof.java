package speedith.core.reasoning.automatic;

import speedith.core.reasoning.Goals;
import speedith.core.reasoning.Proof;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface AutomaticProof {

    Proof generateProof(Goals initialGoals) throws AutomaticProofException;

    Proof extendProof(Proof proof) throws AutomaticProofException;

}
