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

import speedith.core.reasoning.args.RuleArg;

/**
 * A class full of convenience methods for obtaining fully specified selection
 * steps and procedures that translate the resulting selection into rule
 * arguments.
 *  @param <T> the type of rule this object produces given a selection sequence of
 * diagrammatic elements.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class RuleArgsFromSelection<T extends RuleArg> {
    // <editor-fold defaultstate="collapsed" desc="Public Conversion Interface">
    /**
     * Converts the given selection sequence to a rule argument.
     * @param selection a collection of selected diagram elements.
     * @return the resulting rule argument.
     * @throws IllegalArgumentException thrown if the selection sequence cannot
     * be converted to a rule argument because it's either {@code null}, faulty,
     * or incomplete in any sense.
     */
    public abstract T convertToRuleArg(SelectionSequence selection);
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Built-in Selection Converters">
//    private static class 
    // </editor-fold>
}
