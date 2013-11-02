package speedith.core.reasoning.rules.instructions;

import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.selection.ContoursSelectionStep;
import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.core.reasoning.args.selection.SelectionStep;

import java.util.ArrayList;
import java.util.List;

import static java.util.Arrays.asList;

public class SelectContoursInstruction implements RuleApplicationInstruction<MultipleRuleArgs> {

    @Override
    public List<? extends SelectionStep> getSelectionSteps() {
        return asList(new ContoursSelectionStep());
    }

    @Override
    public MultipleRuleArgs extractRuleArg(SelectionSequence selectionSequence, int subgoalIndex) {
        ArrayList<ContourArg> ruleArgs = new ArrayList<>();
        List<RuleArg> selections = selectionSequence.getAcceptedSelectionsForStepAt(0);
        for (RuleArg ruleArg : selections) {
            if (ruleArg instanceof ContourArg) {
                ContourArg contourArg = (ContourArg) ruleArg;
                ruleArgs.add(new ContourArg(subgoalIndex, contourArg.getSubDiagramIndex(), contourArg.getContour()));
            }
        }
        return new MultipleRuleArgs(ruleArgs);
    }
}
