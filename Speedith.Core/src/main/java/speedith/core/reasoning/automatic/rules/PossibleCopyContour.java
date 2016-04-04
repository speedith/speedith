package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.InferenceApplication;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.CopyContours;
import speedith.core.reasoning.rules.CopyContoursTopological;

import java.util.HashSet;
import java.util.Set;

/**
 * A possibility to apply copy contour.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleCopyContour extends PossibleRuleApplication<MultipleRuleArgs> {

    private final String contour;

    public PossibleCopyContour(int subGoalIndex, SpiderDiagramOccurrence target, CopyContoursTopological rule, String contour) {
        super(subGoalIndex, target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public MultipleRuleArgs getArg()  {
        int targetIndex = getTarget().getOccurrenceIndex();
        ContourArg arg = new ContourArg(getSubGoalIndex(), targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }


    @Override
    public boolean isSuperfluous(Proof p) {
        for (InferenceApplication application : p.getInferenceApplications() ) {
            if (application.getInference() instanceof CopyContours) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg();
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


}
