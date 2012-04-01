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
package speedith.ui.selection.helpers;

import java.awt.Frame;
import java.util.ArrayList;
import java.util.List;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.InferenceRuleProvider;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.args.SpiderZoneArg;
import speedith.ui.selection.SelectionDialog;
import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.core.reasoning.args.selection.SelectSpiderFeetStep;

/**
 * Provides selection services for {@link SpiderRegionArg spider region rule
 * arguments}. It provides a GUI for selecting feet of any spider in a diagram.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 * @deprecated Should use the mechanism that comes with {@link InferenceRuleProvider
 * inference rule providers}. See {@link InferenceRuleProvider#getInstructions() }.
 */
@Deprecated
@SelectorDetails(name="Spider region selector", targetRuleArg=SpiderRegionArg.class)
public class SpiderRegionSelector extends DiagramSelector<SpiderRegionArg> {
    private final int subgoalIndex;

    /**
     * Will create rule arguments with sub-goal index 0.
     */
    public SpiderRegionSelector() {
        this(0);
    }

    /**
     * Will create rule arguments with the given sub-goal.
     * @param subgoalIndex 
     */
    public SpiderRegionSelector(int subgoalIndex) {
        if (subgoalIndex < 0) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_INDEX_OUT_OF_RANGE_LOWONLY", "subgoalIndex", "0"));
        }
        this.subgoalIndex = subgoalIndex;
    }
    

    /**
     * An instance of this selector that can be used anywhere (since it is
     * stateless).
     */
    public static final SpiderRegionSelector Instance = new SpiderRegionSelector();

    @Override
    public SpiderRegionArg convertToRuleArg(SelectionSequence selection) {
        List<RuleArg> sel = selection.getAcceptedSelectionsForStepAt(0);
        SpiderZoneArg firstSelection = (SpiderZoneArg) sel.get(0);
        return new SpiderRegionArg(subgoalIndex, firstSelection.getSubDiagramIndex(), firstSelection.getSpider(), getRegionFromFeetSelection(sel));
    }

    @Override
    public SpiderRegionArg showSelectionDialog(Frame parent, SpiderDiagram diagram) {
        SelectionDialog dsd = new SelectionDialog(parent, true, diagram, SelectSpiderFeetStep.getInstance());
        dsd.setVisible(true);
        if (dsd.isCancelled()) {
            return null;
        } else {
            return convertToRuleArg(dsd.getSelection());
        }
    }

    private static Region getRegionFromFeetSelection(List<RuleArg> selection) {
        ArrayList<Zone> zones = new ArrayList<Zone>();
        for (RuleArg sel : selection) {
            if (sel instanceof SpiderZoneArg) {
                SpiderZoneArg curSel = (SpiderZoneArg) sel;
                zones.add(curSel.getZone());
            }
        }
        return new Region(zones);
    }
}