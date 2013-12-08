/*
 *   Project: Speedith.Core
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
package speedith.core.reasoning.rules.instructions;

import speedith.core.lang.Region;
import speedith.core.lang.Zone;
import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.args.SpiderZoneArg;
import speedith.core.reasoning.args.selection.SelectSpiderFeetStep;
import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.core.reasoning.args.selection.SelectionStep;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectFeetOfSpiderInstruction implements RuleApplicationInstruction<SpiderRegionArg> {

    private final List<? extends SelectionStep> steps = Arrays.asList(SelectSpiderFeetStep.getInstance());

    private SelectFeetOfSpiderInstruction() {
    }

    public static SelectFeetOfSpiderInstruction getInstance() {
        return SingletonContainer.Instructions;
    }

    @Override
    public List<? extends SelectionStep> getSelectionSteps() {
        return Collections.unmodifiableList(steps);
    }

    @Override
    public SpiderRegionArg extractRuleArg(SelectionSequence selectionSequence, int subgoalIndex) {
        List<RuleArg> sel = selectionSequence.getAcceptedSelectionsForStepAt(0);
        SpiderZoneArg firstSelection = (SpiderZoneArg) sel.get(0);
        return new SpiderRegionArg(subgoalIndex, firstSelection.getSubDiagramIndex(), firstSelection.getSpider(), getRegionFromFeetSelection(sel));
    }

    private static Region getRegionFromFeetSelection(List<RuleArg> selection) {
        ArrayList<Zone> zones = new ArrayList<>();
        for (RuleArg sel : selection) {
            if (sel instanceof SpiderZoneArg) {
                SpiderZoneArg curSel = (SpiderZoneArg) sel;
                zones.add(curSel.getZone());
            }
        }
        return new Region(zones);
    }

    private static final class SingletonContainer {
        private static final SelectFeetOfSpiderInstruction Instructions = new SelectFeetOfSpiderInstruction();
    }
}
