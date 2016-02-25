package speedith.core.reasoning.automatic;

import java.util.EventObject;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class ProofChangedEvent extends EventObject {

    public ProofChangedEvent(Object source) {
        super(source);
    }
}
