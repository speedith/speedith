package speedith.ui.automatic;

/**
 *  Event to signal that a tactic has been applied to the current proof.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticAppliedEvent extends ProofChangedEvent {

    public TacticAppliedEvent(Object source) {
        super(source);
    }
}
