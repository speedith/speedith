package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by sl542 on 16/11/15.
 */
public class PossibleConjunctionElimination extends PossibleRuleApplication {
    SpiderDiagramWrapper child;
    public PossibleConjunctionElimination(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, SpiderDiagramWrapper child) {
        super(target, rule);
        this.child = child;
    }

    @Override
    public RuleArg getArg(int subgoalindex) {
        SubDiagramIndexArg compound  = new SubDiagramIndexArg(subgoalindex, getTarget().getOccurrenceIndex());
        SubDiagramIndexArg childArg = new SubDiagramIndexArg(subgoalindex, child.getOccurrenceIndex());
        List<SubDiagramIndexArg> args = new ArrayList<>();
        args.add(compound);
        args.add(childArg);
        return new MultipleRuleArgs(args);
    }
}
