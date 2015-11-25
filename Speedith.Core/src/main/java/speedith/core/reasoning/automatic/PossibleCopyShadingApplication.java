package speedith.core.reasoning.automatic;

import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

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
        if (!applied.getCopiedShadings(getTarget()).contains(region)) {
            p.applyRule(getRule(), getArg(subGoalIndex));
            applied.addCopiedShadings(getTarget(), region);
            return true;
        } else {
            return false;
        }
    }
}
