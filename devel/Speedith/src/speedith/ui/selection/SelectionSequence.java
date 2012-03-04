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
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import speedith.ui.SpiderDiagramClickEvent;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SelectionSequence {

    private ArrayList<SelectionStep> selectionSteps;
    private ArrayList<SpiderDiagramClickEvent>[] acceptedSelections;

    /**
     * Creates a new selection sequence with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this method makes a copy of the
     * given collections.</p>
     *
     * @param selectionSteps the selection steps (which will guide the user
     * through the selection process).
     */
    public SelectionSequence(Collection<SelectionStep> selectionSteps) {
        this(selectionSteps == null || selectionSteps.isEmpty()
                ? null
                : new ArrayList<SelectionStep>(selectionSteps));
    }

    /**
     * Creates a new selection sequence with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this method does not make a copy of
     * the given collections.</p>
     *
     * @param selectionSteps the selection steps (which will guide the user
     * through the selection process).
     */
    SelectionSequence(ArrayList<SelectionStep> selectionSteps) {
        if (selectionSteps == null || selectionSteps.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "selectionSteps"));
        }
        this.selectionSteps = selectionSteps;
        this.acceptedSelections = new ArrayList[selectionSteps.size()];
    }

    /**
     * Returns an unmodifiable view of the list of selection clicks for the
     * given step. Returns {@code null} if no click has been accepted for this
     * step.
     *
     * @param stepIndex
     * @return
     */
    public List<SpiderDiagramClickEvent> getAcceptedClicksForStepAt(int stepIndex) {
        if (stepIndex < 0 || stepIndex >= selectionSteps.size()) {
            throw new IndexOutOfBoundsException(speedith.core.i18n.Translations.i18n("GERR_INDEX_OUT_OF_BOUNDS"));
        }
        return (acceptedSelections[stepIndex] == null
                || acceptedSelections[stepIndex].isEmpty())
                ? null
                : Collections.unmodifiableList(acceptedSelections[stepIndex]);
    }

    /**
     * Returns the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     *
     * @return the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     */
    public List<SelectionStep> getSelectionSteps() {
        return Collections.unmodifiableList(selectionSteps);
    }

    public int getSelectionStepsCount() {
        return selectionSteps.size();
    }

    public SelectionStep getSelectionStepAt(int index) {
        return selectionSteps.get(index);
    }

    public int getAcceptedClickCount(int stepIndex) {
        return acceptedSelections[stepIndex] == null ? 0 : acceptedSelections[stepIndex].size();
    }

    protected void addAcceptedClick(int stepIndex, SpiderDiagramClickEvent click) {
        (acceptedSelections[stepIndex] == null
                ? (acceptedSelections[stepIndex] = new ArrayList<SpiderDiagramClickEvent>())
                : acceptedSelections[stepIndex]).add(click);
    }

    protected void clearAcceptedClicks(int stepIndex) {
        if (acceptedSelections[stepIndex] != null) {
            acceptedSelections[stepIndex].clear();
        }
    }
}
