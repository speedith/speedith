package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplication;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.CopyContours;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by sl542 on 17/11/15.
 */
public class PossibleCopyContourApplication extends PossibleRuleApplication {

    private String contour;

    public PossibleCopyContourApplication(SpiderDiagramOccurrence target, InferenceRule<? super RuleArg> rule, String contour) {
        super(target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public RuleArg getArg(int subgoalindex)  {
        int targetIndex = getTarget().getOccurrenceIndex();
        ContourArg arg = new ContourArg(subgoalindex, targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }


    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        for (RuleApplication application : p.getRuleApplications() ) {
            if (application.getInferenceRule() instanceof CopyContours) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs = (MultipleRuleArgs) getArg(subGoalIndex);
                if (args.size() == thisArgs.size() && args.size() > 0) {
                    // application is superfluous if the other rule
                    // a) works on the same subgoal
                    // b) and on the same subdiagram and
                    // c) both refer to the same region
                    ContourArg thisFirst = (ContourArg) thisArgs.get(0);
                    ContourArg thatFirst = (ContourArg) args.get(0);
                    if (thisFirst.getSubgoalIndex() == thatFirst.getSubgoalIndex() && getTarget().getOccurrenceIndex() == thatFirst.getSubDiagramIndex()) {
                        Set<String> thisContours = new HashSet<>();
                        Set<String> thatContours = new HashSet<>();
                        for (int i = 0; i < args.size(); i++) {
                            thisContours.add(((ContourArg) thisArgs.get(i)).getContour());
                            thatContours.add(((ContourArg) args.get(i)).getContour());
                        }
                        if (thisContours.equals(thatContours)) {
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
        applied.removeCopiedContour(getTarget(), getContour());
    }
}
