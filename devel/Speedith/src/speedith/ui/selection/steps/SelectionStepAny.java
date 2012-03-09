/*
 *   Project: Speedith
 * 
 * File name: Class.java
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
package speedith.ui.selection.steps;

import java.util.Locale;
import static speedith.i18n.Translations.i18n;
import speedith.ui.SpiderDiagramClickEvent;
import speedith.ui.SpiderDiagramPanel;
import speedith.ui.selection.SelectionSequence;
import speedith.ui.selection.steps.SelectionStep.SelectionRejectionExplanation;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectionStepAny extends SelectionStep {

    public SelectionStepAny() {
    }

    @Override
    public boolean isFinished(SelectionSequence selection, int thisIndex) {
        return false;
    }

    @Override
    public boolean isSkippable(SelectionSequence selection, int thisIndex) {
        return true;
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        return i18n(locale, "SELECTION_STEP_MSG_ANY");
    }

    @Override
    public SelectionRejectionExplanation acceptClick(SpiderDiagramClickEvent event, SelectionSequence selection, int thisIndex) {
        return null;
    }

    @Override
    public boolean cleanSelectionOnStart() {
        return false;
    }

    @Override
    public int getHighlightingMode() {
        return SpiderDiagramPanel.All;
    }

    @Override
    public SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex) {
        return null;
    }
    
}
