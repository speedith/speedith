package speedith.core.reasoning.automatic.strategies;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.InferenceApplication;
import speedith.core.reasoning.ProofAnalyser;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.rules.*;
import speedith.core.reasoning.rules.util.HeuristicUtils;
import speedith.core.reasoning.rules.util.ReasoningUtils;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class LowClutterStrategy implements Strategy, StrategyProvider {

    private static final String strategyName = "lowclutter_strategy";

    private static final Map<Class, Integer> COSTS = createCosts();

    private static Map<Class, Integer> createCosts() {
        Map<Class, Integer> result = new HashMap<>();
        result.put(IntroContour.class, 5);
        result.put(IntroShadedZone.class, 5);
        result.put(CopyContours.class, 7);
        result.put(CopyShading.class, 7);
        result.put(RemoveContour.class, 3);
        result.put(RemoveShadedZone.class, 3);
        result.put(RemoveShading.class, 3);
        result.put(Combining.class, 2);
        result.put(ConjunctionElimination.class, 2);
        return Collections.unmodifiableMap(result);
    }


    public LowClutterStrategy() {

    }

    @Override
    public int getCost(Proof p) {

        List<InferenceApplication> applications = p.getInferenceApplications();
        int cost = 0;
/*        for (InferenceApplication app: applications) {
            int debug = COSTS.get(app.getInference().getClass());
            cost +=  debug;
        }*/
        return p.getInferenceApplicationCount();
    }

    @Override
    public int getHeuristic(Proof p) throws AutomaticProofException {
        int heuristic = 0;
        for (SpiderDiagram goal : p.getLastGoals().getGoals()) {
            if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
                CompoundSpiderDiagram impl = (CompoundSpiderDiagram) goal;
                heuristic += ProofAnalyser.clutterScore(impl.getOperand(0));
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
        return "Removes Clutter when possible";
    }

    @Override
    public String getPrettyName() {
        return "Keep the amount of Clutter low";
    }

}
