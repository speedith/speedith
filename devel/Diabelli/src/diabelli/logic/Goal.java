/*
 * File name: Goal.java
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
package diabelli.logic;

import diabelli.components.GoalProvidingReasoner;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Represents a proof goal (with premises and conclusions) that are being
 * tackled in a {@link GoalProvidingReasoner goal-providing reasoner}. <p>A goal
 * consists of a list of premise formulae and a single conclusion formula. In
 * short, a goal is a Horn clause: <div style="padding-left: 2em;"><pre>(&#x22C0;<sub>[1 &#x2264;
 * <span style="font-style:italic;">i</span> &#x2264; n]</sub>
 * <span style="font-style:italic;">P<sub>i</sub></span>) &#x27F9;
 * <span style="font-style:italic;">C</span></pre></div> </p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Goal {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final ArrayList<Formula> premises;
    private final Formula conclusion;
    private final Formula goalAsformula;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises the goal with the given premises, conclusion, and a formula
     * that represents the whole goal. <p>Any of the parameters may be {@code null}.</p>
     *
     * @param premises the premises of the goal.
     * @param conclusion the conclusion of the goal.
     * @param goalAsformula the goal represented with a formula.
     */
    public Goal(ArrayList<Formula> premises, Formula conclusion, Formula goalAsformula) {
        this.premises = premises;
        this.conclusion = conclusion;
        this.goalAsformula = goalAsformula;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns the list of premises in this goal. This method will return {@code
     * null} if there are no premises.
     *
     * @return the list of premises in this goal.
     */
    public List<Formula> getPremises() {
        return premises == null || premises.isEmpty() ? null : Collections.unmodifiableList(premises);
    }
    
    /**
     * Returns the number of premises present in this goal.
     * @return the number of premises present in this goal.
     */
    public int getPremisesCount() {
        return premises == null ? 0 : premises.size();
    }

    /**
     * Returns the conclusion of this goal. This method may return {@code
     * null} if this goal has no conclusion.
     *
     * @return the conclusion of this goal.
     */
    public Formula getConclusion() {
        return conclusion;
    }

    /**
     * Returns a formula that represents the whole goal. If the reasoner that
     * owns this goal does not support representation of a whole goal as a
     * formula then this method may return {@code null}.
     *
     * @return a formula that represents the whole goal.
     */
    public Formula asFormula() {
        return goalAsformula;
    }
    // </editor-fold>
}
