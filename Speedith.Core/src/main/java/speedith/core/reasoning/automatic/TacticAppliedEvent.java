package speedith.core.reasoning.automatic;

import speedith.core.reasoning.automatic.ProofChangedEvent;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticAppliedEvent extends ProofChangedEvent {

    public TacticAppliedEvent(Object source) {
        super(source);
    }
}
