package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

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
        if (!applied.getRemovedShading(getTarget()).contains(zone)) {
            p.applyRule(getRule(), getArg(subGoalIndex));
            applied.addRemovedShading(getTarget(), zone);
            return true;
        } else {
            return false;
        }
    }
}
