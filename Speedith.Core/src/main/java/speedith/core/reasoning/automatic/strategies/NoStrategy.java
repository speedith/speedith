package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;

/**
 * Implements a non-strategy, i.e., it just picks the next rule that is available without
 * any further consideration.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class NoStrategy implements Strategy, StrategyProvider {

    private static final String strategyName = "no_strategy";

    /*
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
    */

    @Override
    public int getCost(Proof p) {
        return 0;
    }

    @Override
    public int getHeuristic(Proof p) {
        return 0;
    }

    @Override
    public Strategy getStrategy() {
        return this;
    }

    @Override
    public String getStrategyName() {
        return strategyName;
    }

    @Override
    public String getDescription() {
        return "No strategy";
    }

    @Override
    public String getPrettyName() {
        return "None";
    }
}
