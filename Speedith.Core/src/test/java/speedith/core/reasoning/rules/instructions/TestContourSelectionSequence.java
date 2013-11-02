package speedith.core.reasoning.rules.instructions;

import speedith.core.lang.NullSpiderDiagram;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.selection.ContoursSelectionStep;
import speedith.core.reasoning.args.selection.SelectionSequence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static java.util.Arrays.asList;

public class TestContourSelectionSequence extends SelectionSequence {
    private final ArrayList<ContourArg> contourArg;

    public TestContourSelectionSequence(ContourArg... contourArg) {
        super(NullSpiderDiagram.getInstance(), asList(new ContoursSelectionStep()));
        this.contourArg = new ArrayList<>(asList(contourArg));
    }

    @Override
    public List<RuleArg> getAcceptedSelectionsForStepAt(int stepIndex) {
        return Collections.<RuleArg>unmodifiableList(contourArg);
    }

    @Override
    public int getAcceptedSelectionsCount(int stepIndex) {
        return contourArg.size();
    }
}
