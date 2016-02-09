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
package speedith.core.reasoning.args.selection;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SelectionSequence {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    protected ArrayList<SelectionStep> selectionSteps;
    protected ArrayList<RuleArg>[] acceptedSelections;
    protected SpiderDiagram diagram;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new selection sequence with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this method makes a copy of the
     * given collections.</p>
     *
     * @param diagram the diagram from which we select the elements.
     * @param selectionSteps the selection steps (which will guide the user
     * through the selection process).
     */
    public SelectionSequence(SpiderDiagram diagram, Collection<? extends SelectionStep> selectionSteps) {
        this(diagram, selectionSteps == null || selectionSteps.isEmpty()
                ? null
                : new ArrayList<>(selectionSteps));
    }

    /**
     * Creates a new selection sequence with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this method does not make a copy of
     * the given collections.</p>
     *
     * @param diagram the diagram from which we select the elements.
     * @param selectionSteps the selection steps (which will guide the user
     * through the selection process).
     */
    @SuppressWarnings("unchecked")
    SelectionSequence(SpiderDiagram diagram, ArrayList<SelectionStep> selectionSteps) {
        if (selectionSteps == null || selectionSteps.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "selectionSteps"));
        }
        if (diagram == null) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "diagram"));
        }
        this.diagram = diagram;
        this.selectionSteps = selectionSteps;
        this.acceptedSelections = new ArrayList[selectionSteps.size()];
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns an unmodifiable view of the list of selections for the given
     * step. Returns {@code null} if no selection has been accepted for this
     * step.
     *
     * @param stepIndex the index of the step for which we want the selected
     * elements.
     * @return the elements selected in the given step.
     */
    public List<RuleArg> getAcceptedSelectionsForStepAt(int stepIndex) {
        if (stepIndex < 0 || stepIndex >= selectionSteps.size()) {
            throw new IndexOutOfBoundsException(speedith.core.i18n.Translations.i18n("GERR_INDEX_OUT_OF_BOUNDS"));
        }
        return (acceptedSelections[stepIndex] == null
                || acceptedSelections[stepIndex].isEmpty())
                ? null
                : Collections.unmodifiableList(acceptedSelections[stepIndex]);
    }

    /**
     * Returns the number of selected diagrammatic elements for the given step.
     * @param stepIndex the selection step in which we are interested.
     * @return the number of selected diagrammatic elements for the given step.
     */
    public int getAcceptedSelectionsCount(int stepIndex) {
        return acceptedSelections[stepIndex] == null ? 0 : acceptedSelections[stepIndex].size();
    }

    /**
     * The diagram from which we select the elements.
     * @return the diagram from which we select the elements.
     */
    public SpiderDiagram getDiagram() {
        return diagram;
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

    /**
     * Returns the number of steps the user has to make in this selection
     * process.
     * @return the number of steps the user has to make in this selection
     * process.
     */
    public int getSelectionStepsCount() {
        return selectionSteps.size();
    }

    /**
     * Returns the description of the selection step at the given index.
     * @param index the index of the step to return.
     * @return the description of the selection step at the given index.
     */
    public SelectionStep getSelectionStepAt(int index) {
        return selectionSteps.get(index);
    }
    //</editor-fold>
}
