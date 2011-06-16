/*
 *   Project: Speedith.Core
 * 
 * File name: ProofTrace.java
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
package speedith.core.reasoning;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import speedith.core.lang.SpiderDiagram;

/**
 * This class represents a sequence of applied inference rules with intermediate
 * subgoals (subgoals are lists of spider diagrams).
 * <p>A proof trace starts with a list of spider diagrams and continues with
 * pairs of applied inference rules and their resulting subgoals (the latter is
 * also a list of spider diagrams).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ProofTrace {
    
    // TODO: Provide an 'unmodifiable' wrapper for proof traces (so that proofs
    // can return their proof traces without the fear of them being modified).

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private ArrayList<SpiderDiagram[]> m_subgoals;
    private ArrayList<InferenceRuleApplication> m_inferenceRules;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises a new proof trace with the given initial goal.
     * @param initialGoals the initial goal (may be {@code null} or empty to
     * indicate a proof trace without proof obligations -- an empty proof
     * trace).
     */
    public ProofTrace(Collection<SpiderDiagram> initialGoals) {
        this(initialGoals == null || initialGoals.isEmpty() ? null : initialGoals.toArray(new SpiderDiagram[initialGoals.size()]));
    }

    /**
     * Initialises a new proof trace with the given initial goal.
     * <p><span style="font-weight:bold">Note</span>: this constructor is <span style="font-weight:bold">unsafe</span>
     * as it does not make a copy of the given {@code initialGoals} array. It
     * simply stores it to list of subgoals.</p>
     * @param initialGoals the initial goal (may be {@code null} or empty to
     * indicate a proof trace without proof obligations -- an empty proof
     * trace).
     */
    ProofTrace(SpiderDiagram[] initialGoals) {
        m_subgoals = new ArrayList<SpiderDiagram[]>();
        m_subgoals.add(initialGoals);
    }
    // </editor-fold>

    // TODO: Specify the outward interface: maybe add methods for removing the
    // tail of the proof trace?
    // <editor-fold defaultstate="collapsed" desc="ProofTrace Interface">
    public ProofTrace append(ProofTrace tralingTrace) {
        throw new UnsupportedOperationException();
    }

    public ProofTrace prepend(ProofTrace tralingTrace) {
        throw new UnsupportedOperationException();
    }

    public List<SpiderDiagram> getInitialGoals() {
        return getSubgoalAt(0);
    }

    public List<SpiderDiagram> getSubgoalAt(int index) {
        if (__isSubgoalsListEmpty()) {
            return null;
        } else {
            return __getSubgoalAt(index);
        }
    }

    public List<SpiderDiagram> getLastGoals() {
        return __isSubgoalsListEmpty() ? null : __getSubgoalAt(m_subgoals.size() - 1);
    }
    
    public ProofTrace applyRule(InferenceRule rule) {
        throw new UnsupportedOperationException();
    }
    
    public ProofTrace applyRule(InferenceRule rule, InferenceRuleArgs args) {
        throw new UnsupportedOperationException();
    }
    
    public ProofTrace applyRule(InferenceRuleApplication ruleApplication) {
        throw new UnsupportedOperationException();
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    private List<SpiderDiagram> __getSubgoalAt(int index) {
        final SpiderDiagram[] initialGoal = m_subgoals.get(index);
        if (initialGoal == null || initialGoal.length < 1) {
            return null;
        }
        return Collections.unmodifiableList(Arrays.asList(initialGoal));
    }

    private boolean __isSubgoalsListEmpty() {
        return m_subgoals == null || m_subgoals.isEmpty();
    }
    // </editor-fold>
}
