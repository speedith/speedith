package speedith.core.reasoning.automatic;

import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;

/**
 * Created by sl542 on 12/11/15.
 */
public class PossibleRemoveContourApplication extends PossibleRuleApplication {

    private String contour;

    public PossibleRemoveContourApplication(PrimarySpiderDiagram target, InferenceRule<? super RuleArg> rule, String contour) {
        super(target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public RuleArg getArg(int subgoalindex, SpiderDiagram sd) {
        int targetIndex = sd.getSubDiagramIndex(getTarget());
        ContourArg arg = new ContourArg(subgoalindex, targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }
}
