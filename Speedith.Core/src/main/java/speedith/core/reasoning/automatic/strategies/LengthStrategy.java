package speedith.core.reasoning.automatic.strategies;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class LengthStrategy implements Strategy, StrategyProvider {

    private static final String strategyName = "pure_length_strategy";

    @Override
    public int getCost(Proof p) {
        return p.getInferenceApplicationCount();
    }

    @Override
    public int getHeuristic(Proof p) throws AutomaticProofException {
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
        return "Examines short proof attempts first";
    }

    @Override
    public String getPrettyName() {
        return "Pure Length Strategy";
    }
}
