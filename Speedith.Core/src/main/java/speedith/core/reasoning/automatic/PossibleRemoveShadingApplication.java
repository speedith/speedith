package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
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
}
