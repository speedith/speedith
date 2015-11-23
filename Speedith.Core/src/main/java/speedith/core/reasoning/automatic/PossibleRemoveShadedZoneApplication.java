package speedith.core.reasoning.automatic;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleRemoveShadedZoneApplication extends PossibleRuleApplication {

    private Zone zone;

    public PossibleRemoveShadedZoneApplication(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, Zone zone) {
        super(target, rule);
        this.zone = zone;
    }

    @Override
    public RuleArg getArg(int subgoalindex) throws RuleApplicationException {
        int subDiagramIndex = getTarget().getOccurrenceIndex();
        return new ZoneArg(subgoalindex, subDiagramIndex, zone);
    }

    public Zone getZone() {
        return zone;
    }
}
