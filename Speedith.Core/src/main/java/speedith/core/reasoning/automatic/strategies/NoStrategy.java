package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;

import java.util.Iterator;
import java.util.Set;

/**
 * Implements a non-strategy, i.e., it just picks the next rule that is available without
 * any further consideration.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class NoStrategy implements Strategy {

    @Override
    public PossibleRuleApplication select(Proof p, Set<PossibleRuleApplication> possible) {
        Iterator<PossibleRuleApplication> it = possible.iterator();
        if (it.hasNext()) {
            PossibleRuleApplication selected = it.next();
            it.remove();
            return selected;
        } else {
            return null;
        }
    }
}
