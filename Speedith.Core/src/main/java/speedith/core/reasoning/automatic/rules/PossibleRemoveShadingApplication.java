package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplication;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.RemoveShading;

/**
 * Created by sl542 on 12/11/15.
 */
public class PossibleRemoveShadingApplication extends PossibleRuleApplication {

    private Zone zone;

    public PossibleRemoveShadingApplication(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, Zone zone) {
        super(target, rule);
        this.zone = zone;
    }

    public Zone getZone() {
        return zone;
    }

    @Override
    public RuleArg getArg(int subgoalindex) {
        int targetIndex = getTarget().getOccurrenceIndex();
        return new ZoneArg(subgoalindex, targetIndex, zone);
    }

    @Override
    public boolean apply(Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
//        if (!applied.getRemovedShading(getTarget()).contains(zone)) {
            p.applyRule(getRule(), getArg(subGoalIndex));
//            applied.addRemovedShading(getTarget(), zone);
            return true;
//        } else {
//            return false;
 //       }
    }

    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        for (RuleApplication application : p.getRuleApplications() ) {
            if (application.getInferenceRule() instanceof RemoveShading) {
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
