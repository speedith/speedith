package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.InferenceApplication;
import speedith.core.reasoning.args.MultipleRuleArgs;
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

    public PossibleRemoveShading(int subGoalIndex, SpiderDiagramOccurrence target, RemoveShading rule, Zone zone) {
        super(subGoalIndex, target, rule);
        this.zone = zone;
    }

    public Zone getZone() {
        return zone;
    }

    @Override
    public MultipleRuleArgs getArg() {
        int targetIndex = getTarget().getOccurrenceIndex();
        ZoneArg zoneArg = new ZoneArg(getSubGoalIndex(), targetIndex, zone);
        return new MultipleRuleArgs(zoneArg);
    }


    @Override
    public boolean isSuperfluous(Proof p) {
        for (InferenceApplication application : p.getInferenceApplications()) {
            if (application.getInference() instanceof RemoveShading) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg();
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
