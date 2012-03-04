/*
 *   Project: Speedith
 * 
 * File name: SelectionSequence.java
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import speedith.ui.SpiderDiagramClickEvent;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SelectionSequence {

    private ArrayList<SelectionStep> selectionSteps;
    private ArrayList<ArrayList<SpiderDiagramClickEvent>> acceptedSelections;

    SelectionSequence(ArrayList<SelectionStep> selectionSteps) {
        if (selectionSteps == null || selectionSteps.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "selectionSteps"));
        }
        this.selectionSteps = selectionSteps;
        this.acceptedSelections = new ArrayList<ArrayList<SpiderDiagramClickEvent>>(selectionSteps.size());
    }

    /**
     * Returns an unmodifiable list of selection click for the given step. Returns
     * {@code null} if no click has been accepted for this step.
     * @param stepIndex
     * @return
     */
    public List<SpiderDiagramClickEvent> getAcceptedClicksForStepAt(int stepIndex) {
        if (stepIndex < 0 || stepIndex >= selectionSteps.size()) {
            throw new IndexOutOfBoundsException(speedith.core.i18n.Translations.i18n("GERR_INDEX_OUT_OF_BOUNDS"));
        }
        return (stepIndex >= acceptedSelections.size()
                || acceptedSelections.get(stepIndex) == null
                || acceptedSelections.get(stepIndex).isEmpty())
                ? null
                : Collections.unmodifiableList(acceptedSelections.get(stepIndex));
    }
}
