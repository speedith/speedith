package speedith.ui.tactics;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.tactical.TacticApplicationException;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface TacticMenuItem {

    /**
     * Applies the method of this TacticMenuItem to the given proof.
     * @param proof The proof to which the tactic will be applied to
     * @return the result of applying the tactic to the proof
     * @throws TacticApplicationException If the tactic could not be applied
     */
    Proof apply(Proof proof) throws TacticApplicationException;

    /**
     *
     * @return the name of this menu item
     */
    String getName();

}
