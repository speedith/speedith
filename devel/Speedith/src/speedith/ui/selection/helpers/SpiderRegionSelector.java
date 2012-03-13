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

import icircles.gui.SpiderClickedEvent;
import java.awt.Frame;
import java.util.ArrayList;
import java.util.List;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.icircles.util.ICirclesToSpeedith;
import speedith.ui.SpiderDiagramClickEvent;
import speedith.ui.selection.DiagramSelectionDialog;
import speedith.ui.selection.SelectionSequence;
import speedith.ui.selection.steps.SelectSpiderFeetStep;

/**
 * Provides selection services for {@link SpiderRegionArg spider region rule
 * arguments}. It provides a GUI for selecting feet of any spider in a diagram.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@SelectorDetails(name="Spider region selector", targetRuleArg=SpiderRegionArg.class)
public class SpiderRegionSelector extends DiagramSelector<SpiderRegionArg> {

    /**
     * An instance of this selector that can be used anywhere (since it is
     * stateless).
     */
    public static final SpiderRegionSelector Instance = new SpiderRegionSelector();

    @Override
    public SpiderRegionArg convertToRuleArg(SelectionSequence selection) {
        List<SpiderDiagramClickEvent> sel = selection.getAcceptedClicksForStepAt(0);
        return new SpiderRegionArg(0, sel.get(0).getSubDiagramIndex(), ((SpiderClickedEvent) sel.get(0).getDetailedInfo()).getSpiderName(), getRegionFromFeetSelection(sel));
    }

    @Override
    public SpiderRegionArg showSelectionDialog(Frame parent, SpiderDiagram diagram) {
        DiagramSelectionDialog dsd = new DiagramSelectionDialog(parent, true, diagram, new SelectSpiderFeetStep());
        dsd.setVisible(true);
        if (dsd.isCancelled()) {
            return null;
        } else {
            return convertToRuleArg(dsd.getSelection());
        }
    }

    private static Region getRegionFromFeetSelection(List<SpiderDiagramClickEvent> selection) {
        ArrayList<Zone> zones = new ArrayList<Zone>();
        for (SpiderDiagramClickEvent sel : selection) {
            if (sel.getDetailedInfo() instanceof SpiderClickedEvent) {
                SpiderClickedEvent curSp = (SpiderClickedEvent) sel.getDetailedInfo();
                zones.add(ICirclesToSpeedith.convert(curSp.getZoneOfFoot()));
            }
        }
        return new Region(zones);
    }
}