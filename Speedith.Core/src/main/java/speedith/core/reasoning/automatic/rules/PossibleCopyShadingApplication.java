package speedith.core.reasoning.automatic.rules;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplication;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.CopyShading;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCopyShadingApplication extends PossibleRuleApplication {

    private Set<Zone> region;

    public PossibleCopyShadingApplication(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, Set<Zone> region) {
        super(target, rule);
        this.region = region;
    }

    @Override
    public RuleArg getArg(int subgoalindex)  {
        int targetIndex = getTarget().getOccurrenceIndex();
        List<ZoneArg> args = new ArrayList<>();
        for(Zone z : region) {
            args.add(new ZoneArg(subgoalindex, targetIndex, z));
        }
        return new MultipleRuleArgs(args);
    }

    public Set<Zone> getRegion() {
        return region;
    }

    @Override
    public boolean apply(Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
//        if (!applied.getCopiedShadings(getTarget()).contains(region)) {
            p.applyRule(getRule(), getArg(subGoalIndex));
//            applied.addCopiedShadings(getTarget(), region);
            return true;
    }

    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        for (RuleApplication application : p.getRuleApplications() ) {
            if (application.getInferenceRule() instanceof CopyShading) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs = (MultipleRuleArgs) getArg(subGoalIndex);
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

    @Override
    public void removeFrom(AppliedRules applied) {
        applied.removeCopiedShading(getTarget(), getRegion());
    }
}
