/*
 *   Project: Speedith
 * 
 * File name: RuleArgsFromSelection.java
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

import java.awt.Frame;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.ui.selection.helpers.SpiderRegionRuleArgsSelector;

/**
 * A class full of convenience methods for obtaining fully specified selection
 * steps and procedures that translate the resulting selection into rule
 * arguments.
 *
 * @param <T> the type of rule this object produces given a selection sequence
 * of diagrammatic elements.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class RuleArgsFromSelection<T extends RuleArg> {
    // <editor-fold defaultstate="collapsed" desc="Public Conversion Interface">

    /**
     * Converts the given selection sequence to a rule argument.
     *
     * @param selection a collection of selected diagram elements.
     * @return the resulting rule argument.
     * @throws IllegalArgumentException thrown if the selection sequence cannot
     * be converted to a rule argument because it's either {@code null}, faulty,
     * or incomplete in any sense.
     */
    public abstract T convertToRuleArg(SelectionSequence selection);

    /**
     * Shows the selection dialog for the given diagram and returns the specific
     * rule arguments.
     *
     * @param parent the frame that should "host" the dialog.
     * @param diagram the diagram from which the user should select the spiders.
     * @return the rule arguments as selected by the user. If the user cancelled
     * the selection {@code null} will be returned.
     */
    public abstract T showSelectionDialog(Frame parent, SpiderDiagram diagram);
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Static Methods for getting built-in selectors">
    /**
     * Returns a selection provider for selecting feet of a spider in a diagram.
     * This can be used for example in the {@link SplitSpiders} rule.
     *
     * @return
     */
    public static RuleArgsFromSelection<SpiderRegionArg> getSpiderRegionSelector() {
        return SpiderRegionRuleArgsSelector.Instance;
    }
    // </editor-fold>
}
