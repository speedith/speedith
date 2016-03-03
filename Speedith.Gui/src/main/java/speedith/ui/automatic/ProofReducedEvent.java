package speedith.ui.automatic;

/**
 *  Event to signal that the current proof was reduced to a subgoal within the proof, i.e.,
 *  the subgoals afterwards were removed.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofReducedEvent extends ProofChangedEvent {

    public ProofReducedEvent(Object source) {
        super(source);
    }
}
