package speedith.core.reasoning.automatic.strategies;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.automatic.AutomaticProver;
import speedith.core.reasoning.rules.util.HeuristicUtils;
import speedith.core.reasoning.rules.util.ReasoningUtils;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class BasicHeuristicStrategy implements Strategy, StrategyProvider {

    private static final String strategyName = "basic_strategy";

    @Override
    public int getCost(Proof p) {
        return p.getRuleApplicationCount();
    }

    @Override
    public int getHeuristic(Proof p) throws AutomaticProofException{
        int heuristic = 0;
        for (SpiderDiagram goal : p.getLastGoals().getGoals()) {
            if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
                CompoundSpiderDiagram impl = (CompoundSpiderDiagram) goal;
                heuristic += HeuristicUtils.metric(impl.getOperand(0), impl.getOperand(1));
            } else {
                throw new AutomaticProofException("The current goal is not an implication of conjunctions.");
            }
        }
        return heuristic;
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
        return "A basic heuristic strategy according to Flower and Stapleton";
    }

    @Override
    public String getPrettyName() {
        return "Basic Heuristic Strategy";
    }
}
