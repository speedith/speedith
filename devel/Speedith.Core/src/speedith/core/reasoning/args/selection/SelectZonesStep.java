/*
 *   Project: Speedith
 * 
 * File name: SelectSpiderFeetStep.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package speedith.core.reasoning.args.selection;

import java.util.List;
import java.util.Locale;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderZoneArg;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.reasoning.args.ZoneArg;

/**
 * This selection step asks the user to select zones.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectZonesStep extends SelectionStep {

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private SelectZonesStep() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    public static SelectZonesStep getInstance() {
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
        return false;
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
     *
     * @param sels
     * @param sel
     * @return
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

        private static final SelectZonesStep TheStep = new SelectZonesStep();
    }
    // </editor-fold>
}
