package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.InferenceApplication;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.IntroShadedZone;
import speedith.core.reasoning.rules.RemoveShadedZone;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleIntroShadedZone extends PossibleRuleApplication<MultipleRuleArgs> {

    private final Zone zone;

    public PossibleIntroShadedZone(int subGoalIndex, SpiderDiagramOccurrence target, IntroShadedZone rule, Zone zone) {
        super(subGoalIndex, target, rule);
        this.zone = zone;
    }

    @Override
    public MultipleRuleArgs getArg() {
        int subDiagramIndex = getTarget().getOccurrenceIndex();
        ZoneArg zoneArg = new ZoneArg(getSubGoalIndex(), subDiagramIndex, zone);
        return new MultipleRuleArgs(zoneArg);
    }

    public Zone getZone() {
        return zone;
    }

  /*  @Override
    public boolean apply(Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
        if (!applied.getIntroducedShadedZones(getTarget()).contains(zone)) {
                p.applyRule(getInference(), getArg(subGoalIndex));
            applied.addIntroducedShadedZones(getTarget(), zone);
            return true;
        } else {
            return false;
        }
    }
*/
    @Override
    public boolean isSuperfluous(Proof p) {
        for (int i =0 ; i< p.getInferenceApplicationCount(); i++) {
            InferenceApplication application = p.getInferenceApplicationAt(i);
            if (application.getInference() instanceof RemoveShadedZone) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs = getArg();
                // application is superfluous if :
                // a) both rules work on the same subgoal
                // b) the result of the already applied rule is the premiss of the current rule
                // c) both refer to the same zones

                if (args.getRuleArgs().containsAll(thisArgs.getRuleArgs())) {
                    ZoneArg arg = (ZoneArg) args.get(0);
                    SpiderDiagram result = p.getGoalsAt(i + 1).getGoalAt(arg.getSubgoalIndex()).getSubDiagramAt(arg.getSubDiagramIndex());
                    return getTarget().getDiagram().equals(result);
                }
            } else if (application.getInference() instanceof IntroShadedZone) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs = getArg();
                // application is superfluous if the other rule
                // a) works on the same subgoal
                // b) and on the same subdiagram and
                // c) both refer to the same zone
                if (args.getRuleArgs().containsAll(thisArgs.getRuleArgs())) {
                    return true;
                }
            }
        }
        return false;
    }
}
