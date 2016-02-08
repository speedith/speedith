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
package speedith.core.reasoning.args.selection;

import propity.util.Sequences;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Locale;

import static speedith.core.i18n.Translations.i18n;

/**
 * This selection step asks the user to select an operator (a compound
 * sub-diagram).
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectOperatorStep extends SelectSubDiagramStep {

    private ArrayList<Operator> allowedOperators;

    public SelectOperatorStep(boolean skippable, Operator... allowedOperators) {
        super(skippable);
        if (allowedOperators != null && allowedOperators.length != 0) {
            this.allowedOperators = new ArrayList<>(Arrays.asList(allowedOperators));
        }
    }

    /**
     * Creates an unskippable single spider selection step.
     */
    public SelectOperatorStep() {
        this(false);
    }

    @Override
    public String getInstruction(Locale locale, SelectionSequence selection, int thisIndex) {
        if (allowedOperators == null || allowedOperators.isEmpty()) {
            return i18n(locale, "SELSTEP_SINGLE_OPERATOR");
        } else {
            return i18n(locale, "SELSTEP_SINGLE_OPERATOR_ONE_OF", Sequences.toString(allowedOperators));
        }
    }

    @Override
    public SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex) {
        if (isSelectionSubDiagram(selection)) {
            if (selectionSeq.getAcceptedSelectionsCount(thisIndex) >= 1) {
                return new I18NSelectionRejectionExplanation("SELSTEP_JUST_ONE_OPERATOR");
            }

            SubDiagramIndexArg properSelection = (SubDiagramIndexArg) selection;
            SpiderDiagram sd = selectionSeq.getDiagram().getSubDiagramAt(properSelection.getSubDiagramIndex());
            if (sd instanceof CompoundSpiderDiagram) {
                CompoundSpiderDiagram csd = (CompoundSpiderDiagram) sd;
                if (allowedOperators != null
                        && !allowedOperators.isEmpty()
                        && !allowedOperators.contains(csd.getOperator())) {
                    return new I18NSelectionRejectionExplanation("SELSTEP_OPERATOR_NOT_ONE_OF", Sequences.toString(allowedOperators));
                } else {
                    return null;
                }
            }
        }
        return new I18NSelectionRejectionExplanation("SELSTEP_NOT_AN_OPERATOR");
    }

    @Override
    public int getSelectableElements() {
        return SelectionStep.Operators;
    }

    private static boolean isSelectionSubDiagram(RuleArg selection) {
        return selection != null && SubDiagramIndexArg.class == selection.getClass();
    }
}
