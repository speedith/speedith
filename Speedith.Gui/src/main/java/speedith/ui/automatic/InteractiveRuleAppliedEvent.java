package speedith.ui.automatic;

/**
 *  Event to signal that a rule was successfully applied interactively on the current proof.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class InteractiveRuleAppliedEvent extends ProofChangedEvent {

    public InteractiveRuleAppliedEvent(Object source) {
        super(source);
    }
}
