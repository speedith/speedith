package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.IntroShadedZone;
import speedith.core.reasoning.rules.RemoveShadedZone;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleRemoveShadedZoneApplication extends PossibleRuleApplication {

    private final Zone zone;

    public PossibleRemoveShadedZoneApplication(SpiderDiagramOccurrence target, InferenceRule<? super RuleArg> rule, Zone zone) {
        super(target, rule);
        this.zone = zone;
    }

    @Override
    public RuleArg getArg(int subgoalindex)  {
        int subDiagramIndex = getTarget().getOccurrenceIndex();
        return new ZoneArg(subgoalindex, subDiagramIndex, zone);
    }

    public Zone getZone() {
        return zone;
    }



    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        for (int i = 0; i < p.getRuleApplicationCount(); i++) {
            RuleApplication application = p.getRuleApplicationAt(i);
            if (application.getInferenceRule() instanceof IntroShadedZone) {
                ZoneArg arg = (ZoneArg) application.getRuleArguments();
                ZoneArg nextArg = (ZoneArg) getArg(subGoalIndex);
                // application is superfluous if :
                // a) both rules work on the same subgoal
                // b) the result of the already applied rule is the premiss of the current rule
                // c) both refer to the same zone
                if (nextArg.getSubgoalIndex() == arg.getSubgoalIndex() &&
                        getTarget().getDiagram().equals(
                                p.getGoalsAt(i + 1).getGoalAt(nextArg.getSubgoalIndex()).getSubDiagramAt(arg.getSubDiagramIndex())) &&
                        nextArg.getZone().equals(arg.getZone())) {
                    return true;
                }
            } else if (application.getInferenceRule() instanceof RemoveShadedZone) {
                ZoneArg args = (ZoneArg) application.getRuleArguments();
                ZoneArg thisArgs = (ZoneArg) getArg(subGoalIndex);
                // application is superfluous if the other rule
                // a) works on the same subgoal
                // b) and on the same subdiagram and
                // c) both refer to the same zone
                if (args.getSubgoalIndex() == thisArgs.getSubgoalIndex() &&
                        getTarget().getOccurrenceIndex() == args.getSubDiagramIndex() && thisArgs.getZone().equals(args.getZone())) {
                    return true;
                }
            }
        }
        return false;
    }
}
