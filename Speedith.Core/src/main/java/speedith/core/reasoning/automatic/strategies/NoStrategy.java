package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;

/**
 * Implements a non-strategy, i.e., does not compute any particular costs and
 * heuristic function, but return 0 in every case.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class NoStrategy implements Strategy, StrategyProvider {

    private static final String strategyName = "no_strategy";

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
