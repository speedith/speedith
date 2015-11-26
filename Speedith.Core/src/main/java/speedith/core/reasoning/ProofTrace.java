/*
 *   Project: Speedith.Core
 * 
 * File name: ProofTrace.java
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
package speedith.core.reasoning;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;

/**
 * An implementation of the {@link Proof} interface. <p>This class serves as the
 * main proof-managing tool for Speedith.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ProofTrace implements Proof {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * Contains all goals of this proof trace (including the initial goal).
     */
    private ArrayList<Goals> goals = new ArrayList<Goals>();
    private ArrayList<RuleApplication> ruleApplications = new ArrayList<RuleApplication>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new proof trace with the given initial goals.
     *
     * @param initialGoals the initial goals (the theorem we want to prove).
     * <p><span style="font-weight:bold">Note</span>: this parameter may be
     * {@code null} in which case no goals will be there to prove and no proof
     * steps will be applicable.</p>
     */
    public ProofTrace(Goals initialGoals) {
        // Add the initial goals to the list of all goals
        if (initialGoals != null) {
            goals.add(initialGoals);
        }
    }

    /**
     * Creates a new empty proof trace.
     */
    public ProofTrace() {
        this((Goals) null);
    }

    /**
     * Creates a new proof trace with the given initial goals.
     *
     * @param initialGoals the initial goals (the theorem we want to prove).
     * <p><span style="font-weight:bold">Note</span>: this parameter may be
     * {@code null} in which case no goals will be there to prove and no proof
     * steps will be applicable.</p>
     */
    public ProofTrace(SpiderDiagram... initialGoals) {
        this(Goals.createGoalsFrom(initialGoals));
    }

    /**
     * Creates a new proof trace with the given initial goals.
     *
     * @param initialGoals the initial goals (the theorem we want to prove).
     * <p><span style="font-weight:bold">Note</span>: this parameter may be
     * {@code null} in which case no goals will be there to prove and no proof
     * steps will be applicable.</p>
     */
    public ProofTrace(List<SpiderDiagram> initialGoals) {
        this(Goals.createGoalsFrom(initialGoals));
    }

    /**
     * Copy constructor for this class. Creates a new instance of the lists holding
     * the {@link Goals} and the {@link RuleApplication} instances (which themselves are
     * immutable).
     *
     * @param goals
     * @param ruleApplications
     */
    public ProofTrace(List<Goals> goals, List<RuleApplication> ruleApplications) {
        this.goals = new ArrayList<Goals>(goals);
        this.ruleApplications = new ArrayList<RuleApplication>(ruleApplications);
    }

    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Proof Interface Implementation">
    @Override
    public <TRuleArg extends RuleArg> RuleApplicationResult applyRule(InferenceRule<TRuleArg> rule) throws RuleApplicationException {
        return applyRule(rule, null);
    }

    @Override
    public <TRuleArg extends RuleArg> RuleApplicationResult applyRule(InferenceRule<? super TRuleArg> rule, TRuleArg args) throws RuleApplicationException {
        if (isFinished()) {
            throw new RuleApplicationException(i18n("PROOF_TRACE_FINISHED"));
        }
        RuleApplicationResult appResult = rule.apply(args, getLastGoals());
        if (appResult == null) {
            throw new IllegalStateException(i18n("SRK_RULE_MUST_RETURN_NONNULL_RESULT", rule.getProvider().getInferenceRuleName()));
        }
        // Discharge any null-spider diagrams automatically.
        Goals newGoals = appResult.getGoals();
        if (!newGoals.isEmpty()) {
            ArrayList<SpiderDiagram> remainingGoals = new ArrayList<SpiderDiagram>();
            NullSpiderDiagram nsd = NullSpiderDiagram.getInstance();
            for (SpiderDiagram goal : newGoals.getGoals()) {
                if (!nsd.isSEquivalentTo(goal)) {
                    remainingGoals.add(goal);
                }
            }
            newGoals = Goals.createGoalsFrom(remainingGoals);
        }
        ruleApplications.add(new RuleApplication(rule, args));
//        goals.add(appResult.getGoals());
        goals.add(newGoals);
        return appResult;
    }

    @Override
    public Goals getGoalsAt(int index) {
        return goals.get(index);
    }

    @Override
    public int getGoalsCount() {
        return goals.size();
    }

    @Override
    public Goals getInitialGoals() {
        return goals.isEmpty() ? null : goals.get(0);
    }

    @Override
    public Goals getLastGoals() {
        return goals.isEmpty() ? null : goals.get(goals.size() - 1);
    }

    @Override
    public List<Goals> getGoals() {
        return Collections.unmodifiableList(goals);
    }

    @Override
    public List<RuleApplication> getRuleApplications() {
        return Collections.unmodifiableList(ruleApplications);
    }

    @Override
    public RuleApplication getRuleApplicationAt(int index) {
        return ruleApplications.get(index);
    }

    @Override
    public int getRuleApplicationCount() {
        return ruleApplications.size();
    }

    @Override
    public boolean isFinished() {
        final Goals lastGoals = getLastGoals();
        return lastGoals == null || lastGoals.isEmpty();
    }

    @Override
    public boolean undoStep() {
        if (getRuleApplicationCount() > 0) {
            goals.remove(goals.size() - 1);
            ruleApplications.remove(ruleApplications.size() - 1);
            return true;
        } else {
            return false;
        }
    }
    //</editor-fold>


}
