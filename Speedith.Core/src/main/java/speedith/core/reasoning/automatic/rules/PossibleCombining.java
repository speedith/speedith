package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.Combining;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCombining extends PossibleRuleApplication<SubDiagramIndexArg> {

    public PossibleCombining(int subGoalIndex, SpiderDiagramOccurrence target, Combining rule) {
        super(subGoalIndex, target, rule);
    }

    @Override
    public SubDiagramIndexArg getArg()  {
        return new SubDiagramIndexArg(getSubGoalIndex(), getTarget().getOccurrenceIndex());
    }
}
