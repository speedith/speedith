package speedith.ui.automatic;

/**
 * Event to signal that the current proof was extended by a single proof step.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofExtendedByStepEvent extends ProofChangedEvent {

    public ProofExtendedByStepEvent(Object source) {
        super(source);
    }
}
