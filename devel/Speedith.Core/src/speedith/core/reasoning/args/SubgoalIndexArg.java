/*
 *   Project: Speedith.Core
 * 
 * File name: SubgoalIndexArg.java
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

import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;

/**
 * Instances of this class provide the <span style="font-style:italic;">subgoal
 * index</span> argument to inference rules.
 * <p>The subgoal index indicates which subgoal, specifically, the inference
 * rule should tackle (see the {@link Goals goals} parameter of the {@link
 * InferenceRule inference rule's} {@link
 * InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
 * apply method}).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SubgoalIndexArg implements RuleArg {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private int subgoalIndex;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    public SubgoalIndexArg(int subgoalIndex) {
        this.subgoalIndex = subgoalIndex;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the index of the subgoal on which the {@link InferenceRule
     * inference rule} should act (in its {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * apply method}).
     * @return the index of the subgoal on which the {@link InferenceRule
     * inference rule} should act (in its {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * apply method}).
     */
    public int getSubgoalIndex() {
        return subgoalIndex;
    }
    // </editor-fold>
}
