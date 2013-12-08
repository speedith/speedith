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

import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderZoneArg;

import java.util.List;
import java.util.Locale;

import static speedith.core.i18n.Translations.i18n;

/**
 * This selection step asks the user to select feet of a spider. This step
 * requires that all the selected feet belong to the same spider.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectSpiderFeetStep extends SelectionStep {

    private SelectSpiderFeetStep() {
    }

    /**
     * Returns the single instance of this step.
     *
     * @return the single instance of this step.
     */
    public static SelectSpiderFeetStep getInstance() {
        return SingletonHolder.Instance;
    }

    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        return getSelectionProblem(selection, thisIndex);
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        return false;
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        List<RuleArg> sels = selection.getAcceptedSelectionsForStepAt(thisIndex);
        return sels != null && !sels.isEmpty() && isSelectionValid(selection, thisIndex) == 0;
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        return i18n(locale, "SELSTEP_SELECT_SPIDER_FEET");
    }

    @Override
    public boolean cleanSelectionOnStart() {
        return false;
    }

    @Override
    public SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex) {
        // Did the user click at the right thing
        if (selection instanceof SpiderZoneArg) {
            List<RuleArg> sels = selectionSeq.getAcceptedSelectionsForStepAt(thisIndex);
            // Is there already a foot in the selection?
            if (sels != null && !sels.isEmpty()) {
                // There is already something in the selection. The foot has to
                // be in the same sub-diagram and must belong to the same spider
                // as the others.
                SpiderZoneArg sp = (SpiderZoneArg) sels.get(0);
                SpiderZoneArg sel = (SpiderZoneArg) selection;

                // Is the spider in the same sub-diagram?
                if (sp.getSubDiagramIndex() != sel.getSubDiagramIndex()) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_SPIDER_DIFFERENT_SUBDIAGRAM");
                } else if (!sel.getSpider().equals(sp.getSpider())) {
                    // The selected foot does not belong to the same spider.
                    return new I18NSelectionRejectionExplanation("SELSTEP_DIFFERENT_SPIDER");
                } else if (isAlreadySelected(sels, sel)) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_ALREADY_SELECTED");
                } else {
                    // The selected foot is okay.
                    return null;
                }
            } else {
                // There is nothing in the selection... The foot can be added.
                return null;
            }
        } else {
            // The user did not click on a spider at all but something else...
            return new I18NSelectionRejectionExplanation("SELSTEP_NOT_CLICKED_A_SPIDER_FOOT");
        }
    }

    @Override
    public int getSelectableElements() {
        return SelectionStep.Spiders;
    }

    /**
     * Returns one of the following: <ul><li><span
     * style="font-weight:bold">0</span>: if the selection is valid,</li>
     * <li><span style="font-weight:bold">1</span>: if the selection contains
     * selected elements that are not spiders.</li> <li><span
     * style="font-weight:bold">2</span>: if not all spiders are from the same
     * sub-diagram,</li> <li><span style="font-weight:bold">3</span>: if not all
     * spider feet belong to the same spider.</li> </ul>
     *
     * @param selection the selection sequence in which this selection step
     *                  participates. This object contains currently {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)
     *                  approved} selections.
     * @param thisIndex the index of this step in the given {@link SelectionSequence}.
     */
    private static int isSelectionValid(SelectionSequence selection, int thisIndex) {
        List<RuleArg> sels = selection.getAcceptedSelectionsForStepAt(thisIndex);
        if (sels != null && !sels.isEmpty()) {
            for (RuleArg sel : sels) {
                if (!(sel instanceof SpiderZoneArg)) {
                    return 1;
                }
            }
            SpiderZoneArg firstFoot = (SpiderZoneArg) sels.get(0);
            for (int i = 1; i < sels.size(); i++) {
                SpiderZoneArg sel = (SpiderZoneArg) sels.get(i);
                if (firstFoot.getSubDiagramIndex() != sel.getSubDiagramIndex()) {
                    return 2;
                } else if (!firstFoot.getSpider().equals(sel.getSpider())) {
                    return 3;
                }
            }
        }
        return 0;
    }

    /**
     * Returns an explanation for the problems with the selection as identified
     * by the {@link SelectSpiderFeetStep#isSelectionValid(speedith.ui.selection.SelectionSequence, int)
     * } method.
     *
     * @param selection the selection sequence in which this selection step
     *                  participates. This object contains currently {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)
     *                  approved} selections.
     * @param thisIndex the index of this step in the given {@link SelectionSequence}.
     */
    private static SelectionRejectionExplanation getSelectionProblem(SelectionSequence selection, int thisIndex) {
        switch (isSelectionValid(selection, thisIndex)) {
            case 0:
                return null;
            case 1:
                return new I18NSelectionRejectionExplanation("SELSTEP_NOT_A_SPIDER_FOOT");
            case 2:
                return new I18NSelectionRejectionExplanation("SELSTEP_NOT_ALL_SPIDER_FEET_IN_SAME_SUBDIAGRAM");
            case 3:
                return new I18NSelectionRejectionExplanation("SELSTEP_NOT_ALL_SPIDER_FEET_OF_SAME_SPIDER");
            default:
                throw new IllegalStateException();
        }
    }

    /**
     * Indicates whether a spider's foot has already been selected (whether it
     * is present in the given selection).
     */
    private static boolean isAlreadySelected(List<RuleArg> sels, SpiderZoneArg sel) {
        for (RuleArg oldSel : sels) {
            if (oldSel instanceof SpiderZoneArg) {
                SpiderZoneArg oldSelT = (SpiderZoneArg) oldSel;
                if (oldSelT.getZone().equals(sel.getZone())) {
                    return true;
                }
            }
        }
        return false;
    }

    private static final class SingletonHolder {
        private static final SelectSpiderFeetStep Instance = new SelectSpiderFeetStep();
    }
}
