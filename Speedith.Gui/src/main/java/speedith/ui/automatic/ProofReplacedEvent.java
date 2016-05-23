package speedith.ui.automatic;

/**
 *  Event to signal that the current proof was replaced by a different one.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofReplacedEvent extends ProofChangedEvent {

    public ProofReplacedEvent(Object source) {
        super(source);
    }
}
