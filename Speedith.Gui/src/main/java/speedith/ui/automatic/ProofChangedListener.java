package speedith.ui.automatic;

import java.util.EventListener;

/**
 * Listener for reacting to {@link ProofChangedEvent proof changed events}.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface ProofChangedListener extends EventListener {


    void interactiveRuleApplied(InteractiveRuleAppliedEvent e);

    void tacticApplied(TacticAppliedEvent e);

    void proofReplaced(ProofReplacedEvent e);

    void proofReduced(ProofReducedEvent e);

    void proofExtendedByStep(ProofExtendedByStepEvent e);


}
