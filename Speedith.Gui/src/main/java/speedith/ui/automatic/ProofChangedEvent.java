package speedith.ui.automatic;

import java.util.EventObject;

/**
 * Super class for events that will be fired if a proof was changed by the UI.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class ProofChangedEvent extends EventObject {

    public ProofChangedEvent(Object source) {
        super(source);
    }
}
