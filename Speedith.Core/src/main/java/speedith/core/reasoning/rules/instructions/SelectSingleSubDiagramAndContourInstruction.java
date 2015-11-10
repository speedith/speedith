package speedith.core.reasoning.rules.instructions;

import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.args.selection.*;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Sven Linker
 * Created by sl542 on 10/11/15.
 */
public class SelectSingleSubDiagramAndContourInstruction implements RuleApplicationInstruction<MultipleRuleArgs> {

    @Override
    public List<? extends SelectionStep> getSelectionSteps() {
        SelectSubDiagramStep selectSubDiagramStep = new SelectPrimaryDiagramStep(false);
        ContoursSelectionStep contoursSelectionStep = new ContoursSelectionStep();
        List<SelectionStep> result = new ArrayList<>();
        result.add(selectSubDiagramStep);
        result.add(contoursSelectionStep);
        return result;
    }

    @Override
    public MultipleRuleArgs extractRuleArg(SelectionSequence selectionSequence, int subgoalIndex) {
        ArrayList<SubDiagramIndexArg> ruleArgs = new ArrayList<>();
        List<RuleArg> subDiagrams = selectionSequence.getAcceptedSelectionsForStepAt(0);
        for (RuleArg selectedDiagram : subDiagrams) {
            if (selectedDiagram instanceof SubDiagramIndexArg) {
                SubDiagramIndexArg subDiagramIndexArg = (SubDiagramIndexArg) selectedDiagram;
                ruleArgs.add(new SubDiagramIndexArg(subgoalIndex, subDiagramIndexArg.getSubDiagramIndex()));
            }
        }
        List<RuleArg> selections = selectionSequence.getAcceptedSelectionsForStepAt(1);
        for (RuleArg ruleArg : selections) {
            if (ruleArg instanceof ContourArg) {
                ContourArg contourArg = (ContourArg) ruleArg;
                ruleArgs.add(new ContourArg(subgoalIndex, contourArg.getSubDiagramIndex(), contourArg.getContour()));
            }
        }
        return new MultipleRuleArgs(ruleArgs);
    }
}
