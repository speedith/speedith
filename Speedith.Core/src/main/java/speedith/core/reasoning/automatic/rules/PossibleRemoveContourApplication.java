package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.PrimarySpiderDiagramWrapper;

/**
 * Created by sl542 on 12/11/15.
 */
public class PossibleRemoveContourApplication extends PossibleRuleApplication {

    private String contour;

    public PossibleRemoveContourApplication(PrimarySpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, String contour) {
        super(target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public RuleArg getArg(int subgoalindex) {
        int targetIndex = getTarget().getOccurrenceIndex();
        ContourArg arg = new ContourArg(subgoalindex, targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }

    @Override
    public boolean apply(Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
        if (!applied.getRemovedContours(getTarget()).contains(contour)) {
            p.applyRule(getRule(), getArg(subGoalIndex));
            applied.addRemoveContour(getTarget(), contour);
            return true;
        } else {
            return false;
        }
    }
}