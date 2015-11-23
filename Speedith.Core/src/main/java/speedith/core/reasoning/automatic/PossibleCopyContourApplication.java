package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

/**
 * Created by sl542 on 17/11/15.
 */
public class PossibleCopyContourApplication extends PossibleRuleApplication {

    private String contour;

    public PossibleCopyContourApplication(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule, String contour) {
        super(target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public RuleArg getArg(int subgoalindex) throws RuleApplicationException {
        int targetIndex = getTarget().getOccurrenceIndex();
        if (targetIndex == -1) {
            throw new RuleApplicationException("The target diagram is not an occurrence in the subgoal");
        }
        ContourArg arg = new ContourArg(subgoalindex, targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }
}
