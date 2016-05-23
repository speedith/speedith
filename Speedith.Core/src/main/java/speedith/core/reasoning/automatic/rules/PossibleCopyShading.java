package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.InferenceApplication;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.CopyShading;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCopyShading extends PossibleRuleApplication<MultipleRuleArgs> {

    private final Set<Zone> region;

    public PossibleCopyShading(int subGoalIndex, SpiderDiagramOccurrence target, CopyShading rule, Set<Zone> region) {
        super(subGoalIndex, target, rule);
        this.region = region;
    }

    @Override
    public MultipleRuleArgs getArg()  {
        int targetIndex = getTarget().getOccurrenceIndex();
        List<ZoneArg> args = new ArrayList<>();
        for(Zone z : region) {
            args.add(new ZoneArg(getSubGoalIndex(), targetIndex, z));
        }
        return new MultipleRuleArgs(args);
    }

    public Set<Zone> getRegion() {
        return region;
    }


    @Override
    public boolean isSuperfluous(Proof p) {
        for (InferenceApplication application : p.getInferenceApplications() ) {
            if (application.getInference() instanceof CopyShading) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg();
                if (args.size() == thisArgs.size() && args.size() > 0) {
                    // application is superfluous if the other rule
                    // a) works on the same subgoal
                    // b) and on the same subdiagram and
                    // c) both refer to the same region
                    ZoneArg thisFirst = (ZoneArg) thisArgs.get(0);
                    ZoneArg thatFirst = (ZoneArg) args.get(0);
                    if (thisFirst.getSubgoalIndex() == thatFirst.getSubgoalIndex() && getTarget().getOccurrenceIndex() == thatFirst.getSubDiagramIndex()) {
                        Set<Zone> thisRegion = new HashSet<>();
                        Set<Zone> thatRegion = new HashSet<>();
                        for (int i = 0; i < args.size(); i++) {
                            thisRegion.add(((ZoneArg) thisArgs.get(i)).getZone());
                            thatRegion.add(((ZoneArg) args.get(i)).getZone());
                        }
                        if (thisRegion.equals(thatRegion)) {
                            return true;
                    }
                    }
                }
            }
        }
        return false;
    }

}
