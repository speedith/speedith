package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;

import java.util.Set;

/**
 * A strategy for choosing the next rule to apply to a proof.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface Strategy {

    /**
     * Selects the next rule to apply to the given proof from the set
     * of given possible proof rule applications.
     *
     * @param p the Proof to which the rule shall be applied to
     * @param possible the set of PossibleRuleApplictions for the current goal in p
     * @return the next PossibleRuleApplication according to this strategy
     */
    PossibleRuleApplication select (Proof p, Set<PossibleRuleApplication> possible);
}
