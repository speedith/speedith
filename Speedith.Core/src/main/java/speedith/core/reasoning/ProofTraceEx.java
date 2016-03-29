/*
 *   Project: Speedith.Core
 * 
 * File name: ProofTraceEx.java
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

import speedith.core.reasoning.args.RuleArg;

import java.util.ArrayList;

import static speedith.core.i18n.Translations.i18n;

/**
 * This class represents a sequence of applied inference rules with intermediate
 * subgoals (subgoals are lists of spider diagrams).
 * <p>A proof trace starts with a list of spider diagrams and continues with
 * pairs of applied inference rules and their resulting subgoals (the latter is
 * also a list of spider diagrams).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ProofTraceEx {

    // TODO: Provide an 'unmodifiable' wrapper for proof traces (so that proofs
    // can return their proof traces without the fear of them being modified).
    // <editor-fold defaultstate="collapsed" desc="Fields">
    private Goals initialGoals;
    private ArrayList<InferenceApplication> inferenceRules;
    private ArrayList<InferenceApplicationResult> applicationResults;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises a new proof trace with the given initial goal.
     * @param initialGoals the initial goals (proof obligations). This parameter
     * may be {@code null} or empty to indicate a proof trace without proof
     * obligations -- an empty proof trace.
     */
    public ProofTraceEx(Goals initialGoals) {
        this.initialGoals = initialGoals;
        inferenceRules = new ArrayList<>();
        applicationResults = new ArrayList<>();
    }
    // </editor-fold>

    // TODO: Specify the outward interface: maybe add methods for removing the
    // tail of the proof trace?
    // <editor-fold defaultstate="collapsed" desc="ProofTraceEx Interface">
    public ProofTraceEx append(ProofTraceEx tralingTrace) {
        throw new UnsupportedOperationException();
    }

    public ProofTraceEx prepend(ProofTraceEx tralingTrace) {
        throw new UnsupportedOperationException();
    }

    /**
     * Returns the number of goals (this includes the initial goals).
     * @return the number of goals (this includes the initial goals).
     */
    public int getGoalsCount() {
        return 1 + applicationResults.size();
    }

    /**
     * Returns the initial goal of this proof trace.
     * @return the initial goal of this proof trace.
     */
    public Goals getInitialGoals() {
        return initialGoals;
    }

    /**
     * Returns the subgoals at the given index. At index 0 are the initial
     * goals. At indices <span style="font-style:italic;">i</span>, where
     * <span style="font-style:italic;">i</span> &gt; 0, we have goals that were
     * the results of applying the <span style="font-style:italic;">i</span>-th
     * inference rule.
     * @param index the index of the subgoal to return.
     * @return the subgoal at the given index.
     */
    public Goals getGoalsAt(int index) {
        if (index == 0) {
            return initialGoals;
        } else if (__isAppResultsListEmpty()) {
            return null;
        } else {
            InferenceApplicationResult appResult = applicationResults.get(index - 1);
            if (appResult == null) {
                return null;
            }
            return appResult.getGoals();
        }
    }

    public Goals getLastGoals() {
        return getGoalsAt(getGoalsCount() - 1);
    }

    public ProofTraceEx applyRule(InferenceRule rule) throws RuleApplicationException {
        return applyRule(rule, null);
    }

    public ProofTraceEx applyRule(InferenceRule rule, RuleArg args) throws RuleApplicationException {
        return applyRule(new InferenceApplication(rule, args, RuleApplicationType.INTERACTIVE, ""));
    }

    public ProofTraceEx applyRule(InferenceApplication inferenceApplication) throws RuleApplicationException {
        if (inferenceApplication == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "inferenceApplication"));
        }
        InferenceApplicationResult appResult = inferenceApplication.applyTo(getLastGoals());
        inferenceRules.add(inferenceApplication);
        applicationResults.add(appResult);
        return this;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    private boolean __isAppResultsListEmpty() {
        return applicationResults == null || applicationResults.isEmpty();
    }
    // </editor-fold>
}
