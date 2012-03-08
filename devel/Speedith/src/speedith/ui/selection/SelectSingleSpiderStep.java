/*
 *   Project: Speedith
 * 
 * File name: SelectSingleSpiderStep.java
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
import icircles.gui.SpiderClickedEvent;
import java.util.List;
import java.util.Locale;
import static speedith.i18n.Translations.i18n;
import speedith.ui.SpiderDiagramClickEvent;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectSingleSpiderStep extends SelectionStep {

    private final boolean skippable;

    public SelectSingleSpiderStep(boolean skippable) {
        this.skippable = skippable;
    }

    /**
     * Creates an unskippable single spider selection step.
     */
    public SelectSingleSpiderStep() {
        this(false);
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        List<SpiderDiagramClickEvent> sels = selection.getAcceptedClicksForStepAt(thisIndex);
        // This selection step is finished if all the following conditions are satisfied:
        return sels != null
                && sels.size() == 1 // If a single element has been selected.
                && sels.get(0).getDetailedInfo() instanceof SpiderClickedEvent; // And that element is a spider.
    }

    public boolean isSelectionValid(List<SpiderDiagramClickEvent> sels) {
        if (sels == null || sels.isEmpty()) {
            return true;
        } else if (sels.size() == 1
                && sels.get(0).getDetailedInfo() instanceof SpiderClickedEvent) {
            return true;
        } else {
            return false;
        }
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        return skippable || isFinished(selection, thisIndex);
    }

    @Override
    public String getInstruction(Locale locale) {
        return i18n(locale, "SELSTEP_SINGLE_SPIDER");
    }

    @Override
    public SelectionRejectionExplanation acceptClick(SpiderDiagramClickEvent event, SelectionSequence selection, int thisIndex) {
        if (event.getDetailedInfo() instanceof SpiderClickedEvent) {
            if (selection.getAcceptedClickCount(thisIndex) >= 1) {
                return new I18NSelectionRejectionExplanation("SELSTEP_JUST_ONE_SPIDER");
            } else {
                return null;
            }
        } else {
            return new I18NSelectionRejectionExplanation("SELSTEP_NOT_A_SPIDER");
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

    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        return isSelectionValid(selection.getAcceptedClicksForStepAt(thisIndex))
                ? null
                : new I18NSelectionRejectionExplanation("SELSTEP_SELECTION_INVALID_NOT_A_SPIDER");
    }
}
