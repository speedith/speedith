package speedith.core.reasoning.rules.instructions;

import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderArg;
import speedith.core.reasoning.args.selection.SelectSingleSpiderStep;
import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.core.reasoning.args.selection.SelectionStep;

import java.util.List;

import static java.util.Arrays.asList;

public class SelectSpiderInstruction implements RuleApplicationInstruction<SpiderArg> {

    public List<SelectSingleSpiderStep> selectionSteps = asList(new SelectSingleSpiderStep(false));

    @Override
    public List<? extends SelectionStep> getSelectionSteps() {
        return selectionSteps;
    }

    @Override
    public SpiderArg extractRuleArg(SelectionSequence selectionSequence, int subgoalIndex) {
        List<RuleArg> ruleArguments = selectionSequence.getAcceptedSelectionsForStepAt(0);
        SpiderArg spiderArg = (SpiderArg) ruleArguments.get(0);
        return new SpiderArg(subgoalIndex, spiderArg.getSubDiagramIndex(), spiderArg.getSpider());
    }
}
