/*
 *   Project: Speedith.Core
 * 
 * File name: Proof.java
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

import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.tactical.TacticApplicationException;

import java.io.Serializable;
import java.util.List;

/**
 * This interface outlines how a proof in Speedith looks like.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface Proof extends Serializable {

    /**
     * Applies the rule on the {@link Proof#getLastGoals()  current goals} (if
     * any are left).
     *
     * @param <TRuleArg> The type of the argument that the rule accepts.
     * @param rule the rule to apply on the current goal.
     * @return the result of the rule application.
     * @throws RuleApplicationException thrown if the rule could not be applied
     * for any reason.
     */
    <TRuleArg extends RuleArg> InferenceApplicationResult applyRule(Inference<TRuleArg, ? extends InferenceApplicationResult> rule, RuleApplicationType type, String typeSpecifier) throws RuleApplicationException, TacticApplicationException;

    /**
     * Applies the rule with the given argument on the {@link Proof#getLastGoals()  current goals}
     * (if any are left).
     *
     * @param <TRuleArg> the type of arguments that will be passed to the
     * inference rule.
     * @param rule the rule to apply on the current goal. <span
     * style="font-weight:bold">Note</span>: must not be {@code null}.
     * @param args the arguments that should be passed on to the rule.
     * @return the result of the rule application.
     * @throws RuleApplicationException thrown if the rule could not be applied
     * for any reason (e.g., if the proof is finished).
     */
    <TRuleArg extends RuleArg> InferenceApplicationResult applyRule(Inference<? super TRuleArg, ? extends InferenceApplicationResult> rule, TRuleArg args, RuleApplicationType type, String typeSpecifier) throws RuleApplicationException,TacticApplicationException;

    /**
     * Returns the subgoals at the given index. At index 0 are the initial
     * goals. At indices <span style="font-style:italic;">i</span>, where <span
     * style="font-style:italic;">i</span> &gt; 0, we have goals that were the
     * results of applying the <span style="font-style:italic;">i</span>-th
     * inference rule.
     *
     * @param index the index of the subgoal to return.
     * @return the subgoal at the given index.
     */
    Goals getGoalsAt(int index);

    /**
     * Returns the number of goals (this includes the initial goals).
     *
     * @return the number of goals (this includes the initial goals).
     */
    int getGoalsCount();

    /**
     * Returns the initial goal of this proof trace. <p><span
     * style="font-weight:bold">Note</span>: this method might return {@code null}
     * to indicate that there are no initial goals.</p>
     *
     * @return the initial goal of this proof trace.
     */
    Goals getInitialGoals();

    /**
     * Returns the pending goals. <p><span style="font-weight:bold">Note</span>:
     * an empty goal indicates that the proof is finished.</p><p><span
     * style="font-weight:bold">Note</span>: this method might return {@code null}
     * to indicate that there are no pending goals.</p>
     *
     * @return the pending goals.
     */
    Goals getLastGoals();

    /**
     * Returns an unmodifiable list of goals in this proof.
     *
     * @return an unmodifiable list of goals in this proof.
     */
    List<Goals> getGoals();

    /**
     * Returns an unmodifiable list of rule applications in this proof.
     *
     * @return an unmodifiable list of rule applications in this proof.
     */
    List<InferenceApplication> getInferenceApplications();

    /**
     * Returns the rule application at the given index.
     *
     * @param index the index of the rule application information to get.
     * @return the rule application at the given index.
     */
    InferenceApplication getInferenceApplicationAt(int index);

    /**
     * Returns the number of rule application in this proof.
     *
     * @return the number of rule application in this proof.
     */
    int getInferenceApplicationCount();

    /**
     * Indicates whether the proof is finished (i.e. whether there are any goals
     * left, goals on which we can still apply inference rules). <p><span
     * style="font-weight:bold">Note</span>: The call to this function is
     * similar to something like this: {@code getLastGoals() == null || getLastGoals().isEmpty()}</p>
     *
     * @return a value that indicates whether the proof is finished.
     */
    boolean isFinished();

    /**
     * Removes the last application of an inference rule (if any).
     *
     * @return returns {@code true} if and only if a goal and a rule application
     * descriptor have been removed. Otherwise, {@code false} is returned, in
     * which case no change at all happens to this proof.
     */
    boolean undoStep();


    /**
     * Creates a version of the this Proof object where all tactic applications
     * are replaced with the applications of the rules used in the tactic.
     *
     * The created proofs may be very long!
     *
     * @return a flattened version of this proof
     */
    Proof createFlattenedProof() throws TacticApplicationException;
}
