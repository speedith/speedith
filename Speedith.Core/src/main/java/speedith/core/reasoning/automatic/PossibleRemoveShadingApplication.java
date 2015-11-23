package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;

/**
 * Created by sl542 on 12/11/15.
 */
public class PossibleRemoveShadingApplication extends PossibleRuleApplication {

    private Zone zone;

    public PossibleRemoveShadingApplication(SpiderDiagram target, InferenceRule<? super RuleArg> rule, Zone zone) {
        super(target, rule);
        this.zone = zone;
    }

    public Zone getZone() {
        return zone;
    }

    @Override
    public RuleArg getArg(int subgoalindex, SpiderDiagram sd) {
        int targetIndex = sd.getSubDiagramIndex(getTarget());
        return new ZoneArg(subgoalindex, targetIndex, zone);
    }
}
