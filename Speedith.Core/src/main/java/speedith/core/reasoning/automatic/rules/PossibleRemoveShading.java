package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplication;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.RemoveShading;

/**
 * A possibility to apply remove shading.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleRemoveShading extends PossibleRuleApplication<MultipleRuleArgs> {

    private final Zone zone;

    public PossibleRemoveShading(SpiderDiagramOccurrence target, RemoveShading rule, Zone zone) {
        super(target, rule);
        this.zone = zone;
    }

    public Zone getZone() {
        return zone;
    }

    @Override
    public MultipleRuleArgs getArg(int subgoalindex) {
        int targetIndex = getTarget().getOccurrenceIndex();
        ZoneArg zoneArg = new ZoneArg(subgoalindex, targetIndex, zone);
        return new MultipleRuleArgs(zoneArg);
    }


    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        for (RuleApplication application : p.getRuleApplications()) {
            if (application.getInferenceRule() instanceof RemoveShading) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg(subGoalIndex);
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
