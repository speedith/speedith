/*
 *   Project: Speedith.Core
 * 
 * File name: DiagramIndexArg.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
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
package speedith.core.reasoning.args;

/**
 * Along with the {@link SubgoalIndexArg subgoal index} this class also
 * provides the <span style="font-style:italic;">diagram index</span>.
 * <p>The diagram index is the number assigned to every sub-diagram and
 * indicates its order of appearance (from left to right) in the whole spider
 * diagram.</p>
 * <p>Note: the containing (parent) diagram takes a lower index than its
 * children.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class DiagramIndexArg extends SubgoalIndexArg implements RuleArg {
    // <editor-fold defaultstate="collapsed" desc="Fields">
    private int primarySDIndex;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    public DiagramIndexArg(int subgoalIndex, int primarySDIndex) {
        super(subgoalIndex);
        this.primarySDIndex = primarySDIndex;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    public int getSubDiagramIndex() {
        return primarySDIndex;
    }
    // </editor-fold>
}
