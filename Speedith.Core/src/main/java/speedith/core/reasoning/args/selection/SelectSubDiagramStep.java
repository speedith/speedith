package speedith.core.reasoning.args.selection;

import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.List;
import java.util.Locale;

import static speedith.core.i18n.Translations.i18n;

public class SelectSubDiagramStep extends SelectionStep {
    protected final boolean skippable;

    public SelectSubDiagramStep(boolean skippable) {
        this.skippable = skippable;
    }

    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        return SelectSubDiagramStep.isSubDiagramSelectionValid(selection.getAcceptedSelectionsForStepAt(thisIndex))
                ? null
                : new I18NSelectionRejectionExplanation("SELSTEP_SINGLE_SUBDIAGRAM_INVALID");
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        return i18n(locale, "SELSTEP_SINGLE_SUBDIAGRAM_EXPLANATION");
    }

    @Override
    public int getSelectableElements() {
        return All;
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        return skippable || isFinished(selection, thisIndex);
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        return isSubDiagramSelectionFinished(selection.getAcceptedSelectionsForStepAt(thisIndex));
    }

    @Override
    public boolean cleanSelectionOnStart() {
        return false;
    }

    @Override
    public SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex) {
        if (isSelectionSubclassOfSubDiagram(selection)) {
            if (selectionSeq.getAcceptedSelectionsCount(thisIndex) >= 1) {
                return new I18NSelectionRejectionExplanation("SELSTEP_JUST_ONE_SUBDIAGRAM");
            }
            return null;
        }
        return new I18NSelectionRejectionExplanation("SELSTEP_SINGLE_SUBDIAGRAM_INVALID");
    }

    public static boolean isSubDiagramSelectionFinished(List<RuleArg> selections) {
        return selections != null &&
               selections.size() == 1 &&
               selections.get(0) instanceof SubDiagramIndexArg; // And that element is a subdiagram.
    }

    public static boolean isSubDiagramSelectionValid(List<RuleArg> selections) {
        return selections == null ||
               selections.isEmpty() ||
               isSubDiagramSelectionFinished(selections);
    }

    private static boolean isSelectionSubclassOfSubDiagram(RuleArg selection) {
        return selection instanceof SubDiagramIndexArg;
    }
}
