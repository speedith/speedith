package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCombiningApplication extends PossibleRuleApplication {

    public PossibleCombiningApplication(SpiderDiagramOccurrence target, InferenceRule<? super RuleArg> rule) {
        super(target, rule);
    }

    @Override
    public RuleArg getArg(int subgoalindex)  {
        return new SubDiagramIndexArg(subgoalindex, getTarget().getOccurrenceIndex());
    }
}
