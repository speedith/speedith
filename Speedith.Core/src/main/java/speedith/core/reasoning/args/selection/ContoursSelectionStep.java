package speedith.core.reasoning.args.selection;

import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.RuleArg;

import java.util.Locale;

public class ContoursSelectionStep extends SelectionStep {
    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        return null;
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        return false;
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        return selection.getAcceptedSelectionsCount(thisIndex) > 0;
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        return "Select a contour";
    }

    @Override
    public SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex) {
        if (selection instanceof ContourArg) {
            return null;
        } else {
            return new I18NSelectionRejectionExplanation("The selected element is not a contour.");
        }
    }

    @Override
    public boolean cleanSelectionOnStart() {
        return true;
    }

    @Override
    public int getSelectableElements() {
        return SelectionStep.Contours;
    }
}
