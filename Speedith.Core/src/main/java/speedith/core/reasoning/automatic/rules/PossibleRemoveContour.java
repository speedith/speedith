package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplication;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.wrappers.PrimarySpiderDiagramOccurrence;
import speedith.core.reasoning.rules.IntroContour;
import speedith.core.reasoning.rules.RemoveContour;

import java.util.HashSet;
import java.util.Set;

/**
 * A possibility to apply remove contour.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleRemoveContour extends PossibleRuleApplication<MultipleRuleArgs> {

    private final String contour;

    public PossibleRemoveContour(PrimarySpiderDiagramOccurrence target, RemoveContour rule, String contour) {
        super(target, rule);
        this.contour = contour;
    }

    public String getContour() {
        return contour;
    }

    @Override
    public MultipleRuleArgs getArg(int subgoalindex) {
        int targetIndex = getTarget().getOccurrenceIndex();
        ContourArg arg = new ContourArg(subgoalindex, targetIndex, contour);
        return new MultipleRuleArgs(arg);
    }

    @Override
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        boolean result = false;
        for (int i =0; i< p.getRuleApplicationCount();i++) {
            RuleApplication application = p.getRuleApplicationAt(i);
            if (application.getInferenceRule() instanceof IntroContour) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg(subGoalIndex);
                // application is superfluous if for all elements of the multiple arguments:
                // a) both work on the same subgoal
                // b) the result of the already applied rule is the premiss of the current rule
                // c) both refer to the same contour
                if (args.size() == thisArgs.size()) {

                    for (int j = 0; j < thisArgs.size(); j++) {
                        ContourArg thisArg = (ContourArg) thisArgs.get(j);
                        ContourArg arg = (ContourArg) args.get(j);
                        result = result || (thisArg.getSubgoalIndex() == arg.getSubgoalIndex() &&
                                getTarget().getDiagram().equals(
                                        p.getGoalsAt(i+1).getGoalAt(thisArg.getSubgoalIndex()).getSubDiagramAt(arg.getSubDiagramIndex())) &&
                                thisArg.getContour().equals(arg.getContour()));
                    }
                }
            }  else if (application.getInferenceRule() instanceof RemoveContour) {
                MultipleRuleArgs args = (MultipleRuleArgs) application.getRuleArguments();
                MultipleRuleArgs thisArgs =  getArg(subGoalIndex);
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
                        for (int j = 0; j < args.size(); j++) {
                            thisContours.add(((ContourArg) thisArgs.get(j)).getContour());
                            thatContours.add(((ContourArg) args.get(j)).getContour());
                        }
                        if (thisContours.equals(thatContours)) {
                            return true;
                        }
                    }
                }
            }
        }
        return result;
    }
}
