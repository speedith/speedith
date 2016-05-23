package speedith.core.reasoning.args.selection;

import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;

import java.util.List;
import java.util.Locale;

import static speedith.core.i18n.Translations.i18n;

/**
 * A selection step denoting the necessity to select a single
 * zone from within a diagram.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class SelectSingleZoneStep extends SelectionStep {
    private SelectSingleZoneStep() {
    }

    public static SelectSingleZoneStep getInstance() {
        return SingletonContainer.TheStep;
    }

    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        if (selection.getAcceptedSelectionsCount(thisIndex) > 0) {
            throw new IllegalStateException(i18n("SELSTEP_INIT_ZONES_PRESENT"));
        }
        return null;
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        return isFinished(selection.getAcceptedSelectionsForStepAt(thisIndex));
    }

    private static boolean isFinished(List<RuleArg> sels) {
        // This selection step is finished if all the following conditions are satisfied:
        return sels != null
                && sels.size() == 1 // If a single element has been selected.
                && sels.get(0) instanceof ZoneArg; // And that element is a spider.
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        return selection.getAcceptedSelectionsCount(thisIndex) > 0;
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        return i18n(locale, "SELSTEP_SELECT_ZONES");
    }

    @Override
    public boolean cleanSelectionOnStart() {
        return true;
    }

    @Override
    public SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex) {
        // Did the user click at the right thing
        if (selection instanceof ZoneArg) {
            List<RuleArg> sels = selectionSeq.getAcceptedSelectionsForStepAt(thisIndex);
            // Is there already a zone in the selection?
            if (sels != null && !sels.isEmpty()) {
                // There is already something in the selection. The zone has to
                // be in the same sub-diagram and must not have already been
                // selected.
                ZoneArg sp = (ZoneArg) sels.get(0);
                ZoneArg sel = (ZoneArg) selection;

                // Is the zone in the same sub-diagram?
                if (sp.getSubDiagramIndex() != sel.getSubDiagramIndex()) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_ZONE_DIFFERENT_SUBDIAGRAM");
                } else if (isAlreadySelected(sels, sel)) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_ALREADY_SELECTED");
                } else {
                    // The selected zone is okay.
                    return null;
                }
            } else {
                // There is nothing in the selection... The zone can be added.
                return null;
            }
        } else {
            // The user did not click on a zone at all but something else...
            return new I18NSelectionRejectionExplanation("SELSTEP_NOT_CLICKED_A_ZONE");
        }
    }

    @Override
    public int getSelectableElements() {
        return SelectionStep.Zones;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    /**
     * Indicates whether a zone has already been selected (whether it is present
     * in the given selection).
     */
    private static boolean isAlreadySelected(List<RuleArg> sels, ZoneArg sel) {
        for (RuleArg oldSel : sels) {
            if (oldSel instanceof ZoneArg) {
                ZoneArg oldSelT = (ZoneArg) oldSel;
                if (oldSelT.getZone().equals(sel.getZone())) {
                    return true;
                }
            }
        }
        return false;
    }
    // </editor-fold>


    // <editor-fold defaultstate="collapsed" desc="Singleton Container Helper">
    private static final class SingletonContainer {

        private static final SelectSingleZoneStep TheStep = new SelectSingleZoneStep();
    }
    // </editor-fold>
}
