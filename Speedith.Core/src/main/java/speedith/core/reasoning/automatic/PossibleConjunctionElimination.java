package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;

/**
 * Created by sl542 on 16/11/15.
 */
public class PossibleConjunctionElimination extends PossibleRuleApplication {
    public PossibleConjunctionElimination(SpiderDiagram target, InferenceRule<? super RuleArg> rule) {
        super(target, rule);
    }

    @Override
    public RuleArg getArg(int subgoalindex, SpiderDiagram sd) {
        return new SubDiagramIndexArg(subgoalindex, sd.getSubDiagramIndex(getTarget()));
    }
}
