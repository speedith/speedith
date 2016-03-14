package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.Combining;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCombiningApplication extends PossibleRuleApplication<SubDiagramIndexArg> {

    public PossibleCombiningApplication(SpiderDiagramOccurrence target, Combining rule) {
        super(target, rule);
    }

    @Override
    public SubDiagramIndexArg getArg(int subgoalindex)  {
        return new SubDiagramIndexArg(subgoalindex, getTarget().getOccurrenceIndex());
    }
}
