package speedith.core.reasoning.rules.instructions;

import speedith.core.lang.Operator;
import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.args.selection.SelectOperatorStep;
import speedith.core.reasoning.args.selection.SelectSubDiagramStep;
import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.core.reasoning.args.selection.SelectionStep;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class SelectOperatorAndSubDiagramInstruction implements RuleApplicationInstruction<MultipleRuleArgs> {

    private List<SelectionStep> step;

    public SelectOperatorAndSubDiagramInstruction(Operator... allowedOperators) {
        List<? extends SelectionStep> temp = Arrays.asList(new SelectOperatorStep(false, allowedOperators));
        List<SelectionStep> result = new ArrayList<>();
        result.addAll(temp);
        result.add(new SelectSubDiagramStep(false));
        step = Collections.unmodifiableList(result);
    }

    @Override
    public List<? extends SelectionStep> getSelectionSteps() {
        return step;
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
            if (ruleArg instanceof SubDiagramIndexArg) {
                SubDiagramIndexArg contourArg = (SubDiagramIndexArg) ruleArg;
                ruleArgs.add(new SubDiagramIndexArg(subgoalIndex, contourArg.getSubDiagramIndex()));
            }
        }
        return new MultipleRuleArgs(ruleArgs);
    }
}
