package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

/**
 * Created by sl542 on 16/11/15.
 */
public class PossibleConjunctionElimination extends PossibleRuleApplication {
    public PossibleConjunctionElimination(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule) {
        super(target, rule);
    }

    @Override
    public RuleArg getArg(int subgoalindex) {
        return new SubDiagramIndexArg(subgoalindex, getTarget().getOccurrenceIndex());
    }
}
