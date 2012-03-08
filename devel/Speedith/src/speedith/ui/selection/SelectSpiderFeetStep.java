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
package speedith.ui.selection;

import icircles.gui.CirclesPanel2;
import icircles.gui.DiagramClickEvent;
import icircles.gui.SpiderClickedEvent;
import java.util.List;
import java.util.Locale;
import static speedith.i18n.Translations.i18n;
import speedith.ui.SpiderDiagramClickEvent;

/**
 *
 *      @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectSpiderFeetStep extends SelectionStep {

    public int isSelectionValid(SelectionSequence selection, int thisIndex) {
        List<SpiderDiagramClickEvent> sels = selection.getAcceptedClicksForStepAt(thisIndex);
        if (sels != null && !sels.isEmpty()) {
            for (SpiderDiagramClickEvent sel : sels) {
                if (!(sel.getDetailedInfo() instanceof SpiderClickedEvent)) {
                    return 1;
                }
            }
            SpiderDiagramClickEvent firstFoot = sels.get(0);
            SpiderClickedEvent firstSpInfo = (SpiderClickedEvent) sels.get(0).getDetailedInfo();
            for (int i = 1; i < sels.size(); i++) {
                SpiderDiagramClickEvent sel = sels.get(i);
                SpiderClickedEvent spInfo = (SpiderClickedEvent) sels.get(i).getDetailedInfo();
                if (firstFoot.getSubDiagramIndex() != sel.getSubDiagramIndex()) {
                    return 2;
                }
                if (firstSpInfo.getFoot().getSpider() != spInfo.getFoot().getSpider()) {
                    return 3;
                }
            }
        }
        return 0;
    }

    private SelectionRejectionExplanation getSelectionProblem(SelectionSequence selection, int thisIndex) {
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
        List<SpiderDiagramClickEvent> sels = selection.getAcceptedClicksForStepAt(thisIndex);
        return sels != null && !sels.isEmpty() && isSelectionValid(selection, thisIndex) == 0;
    }

    @Override
    public String getInstruction(Locale locale) {
        return i18n(locale, "SELSTEP_SELECT_SPIDER_FEET");
    }

    @Override
    public SelectionRejectionExplanation acceptClick(SpiderDiagramClickEvent event, SelectionSequence selection, int thisIndex) {
        // Did the user click at the right thing
        if (event.getDetailedInfo() instanceof SpiderClickedEvent) {
            List<SpiderDiagramClickEvent> sels = selection.getAcceptedClicksForStepAt(thisIndex);
            // Is there already a foot in the selection?
            if (sels != null && !sels.isEmpty()) {
                // There is already something in the selection. The foot has to
                // be in the same sub-diagram and must belong to the same spider
                // as the others.
                SpiderClickedEvent sp = (SpiderClickedEvent) sels.get(0).getDetailedInfo();

                // Is the spider in the same sub-diagram?
                if (sels.get(0).getSubDiagramIndex() != event.getSubDiagramIndex()) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_SPIDER_DIFFERENT_SUBDIAGRAM");
                } else if (sp.getFoot().getSpider() != ((SpiderClickedEvent) event.getDetailedInfo()).getFoot().getSpider()) {
                    // The selected foot does not belong to the same spider.
                    return new I18NSelectionRejectionExplanation("SELSTEP_DIFFERENT_SPIDER");
                } else if (isAlreadySelected(sels, (SpiderClickedEvent) event.getDetailedInfo())) {
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
    public boolean cleanSelectionOnStart() {
        return false;
    }

    @Override
    public int getHighlightingMode() {
        return CirclesPanel2.Spiders;
    }

    private boolean isAlreadySelected(List<SpiderDiagramClickEvent> sels, SpiderClickedEvent event) {
        for (SpiderDiagramClickEvent sel : sels) {
            if (sel.getDetailedInfo() instanceof SpiderClickedEvent) {
                SpiderClickedEvent selSp = (SpiderClickedEvent) sel.getDetailedInfo();
                if (selSp.getFoot() == event.getFoot()) {
                    return true;
                }
            }
        }
        return false;
    }
}
