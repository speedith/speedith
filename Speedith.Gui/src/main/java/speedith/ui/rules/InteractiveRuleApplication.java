/*
 *   Project: Speedith
 * 
 * File name: InteractiveRuleApplication.java
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
package speedith.ui.rules;

import javax.swing.JFrame;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.ui.selection.SelectSubgoalDialog;
import speedith.ui.selection.SelectionDialog;

/**
 * This class contains static utility methods for interactive application of
 * inference rules on goals within a proof. The most useful method will probably
 * be {@link InteractiveRuleApplication#applyRuleInteractively(java.lang.String,
 * speedith.core.lang.SpiderDiagram)}
 * }.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class InteractiveRuleApplication {

    private InteractiveRuleApplication() {
    }

    //<editor-fold defaultstate="collapsed" desc="Rule Application With Subgoal Index">
    /**
     * Applies the inference rule with the given name on the subgoal with the
     * specified index in the provided proof. This method interactively asks the
     * user to provide additional information for the inference rule (if the
     * inference rule requires it).
     *
     * @param window this window will be used as the parent of all opened modal
     * dialogs.
     * @param ruleName the inference rule to apply.
     * @param proof the proof that contains the goals on which to apply the
     * inference rule.
     * @return {@code true} if the inference rule was applied. If the user
     * cancelled the process {@code false} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static boolean applyRuleInteractively(JFrame window, String ruleName,  Proof proof) throws RuleApplicationException,TacticApplicationException {
        return applyRuleInteractively(window, InferenceRules.getInferenceRule(ruleName),  proof);
    }

    /**
     * Applies the inference rule with the given name on the subgoal with the
     * specified index in the provided proof. This method interactively asks the
     * user to provide additional information for the inference rule (if the
     * inference rule requires it).
     *
     * @param window this window will be used as the parent of all opened modal
     * dialogs.
     * @param rule the inference rule to apply.
     * @param proof the proof that contains the goals on which to apply the
     * inference rule.
     * @return {@code true} if the inference rule was applied. If the user
     * cancelled the process {@code false} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static boolean applyRuleInteractively(JFrame window, InferenceRule<? extends RuleArg> rule,  Proof proof) throws RuleApplicationException, TacticApplicationException {
        return applyRuleInteractively(window, rule, proof, null) != null;
    }

    /**
     * Applies the inference rule with the given name on the subgoal with the
     * specified index in the provided goals. This method interactively asks the
     * user to provide additional information for the inference rule (if the
     * inference rule requires it).
     *
     * @param window this window will be used as the parent of all opened modal
     * dialogs.
     * @param rule the inference rule to apply.
     * @param goals the goals on which to apply the inference rule.
     * @return the result of the rule application. However, if the user
     * cancelled the process {@code null} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static InferenceApplicationResult applyRuleInteractively(JFrame window, InferenceRule<? extends RuleArg> rule, Goals goals) throws RuleApplicationException, TacticApplicationException {
        return applyRuleInteractively(window, rule,  null, goals);
    }

    /**
     * Applies the inference rule with the given name on the subgoal with the
     * specified index in the provided goals. This method interactively asks the
     * user to provide additional information for the inference rule (if the
     * inference rule requires it).
     *
     * @param window this window will be used as the parent of all opened modal
     * dialogs.
     * @param rule the inference rule to apply.
     * @param subgoalIndex the index of the subgoal on which to apply the rule.
     * @param goals the goals on which to apply the inference rule.
     * @return the result of the rule application. However, if the user
     * cancelled the process {@code null} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
//    public static InferenceApplicationResult applyRuleInteractively(JFrame window, String rule, Goals goals) throws RuleApplicationException, TacticApplicationException {
//        return applyRuleInteractively(window, InferenceRules.getInferenceRule(rule), null, goals);
//    }

    /**
     * Applies the inference rule with the given name on the first subgoal in
     * the provided goals. This method interactively asks the user to provide
     * additional information for the inference rule (if the inference rule
     * requires it).
     *
     * @param window this window will be used as the parent of all opened modal
     * dialogs.
     * @param rule the inference rule to apply.
     * @param goals the goals on which to apply the inference rule.
     * @return the result of the rule application. However, if the user
     * cancelled the process {@code null} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static InferenceApplicationResult applyRuleInteractively(JFrame window, String rule, Goals goals) throws RuleApplicationException, TacticApplicationException {
        return applyRuleInteractively(window, InferenceRules.getInferenceRule(rule), null, goals);
    }

    /**
     * Applies the inference rule with the given name on the first subgoal in
     * the provided goals. This method interactively asks the user to provide
     * additional information for the inference rule (if the inference rule
     * requires it).
     *
     * @param rule the inference rule to apply.
     * @param goals the goals on which to apply the inference rule.
     * @return the result of the rule application. However, if the user
     * cancelled the process {@code null} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static InferenceApplicationResult applyRuleInteractively(String rule, Goals goals) throws RuleApplicationException, TacticApplicationException {
        return applyRuleInteractively(null, InferenceRules.getInferenceRule(rule), null, goals);
    }

    /**
     * Applies the inference rule with the given name on the provided spider
     * diagram. This method interactively asks the user to provide additional
     * information for the inference rule (if the inference rule requires it).
     *
     * @param rule the inference rule to apply.
     * @param diagram the diagram on which to apply the inference rule.
     * @return the result of the rule application. However, if the user
     * cancelled the process {@code null} is returned.
     * @throws RuleApplicationException this exception is thrown if the rule
     * application failed (while the rule was being applied). This could be due
     * to invalid arguments or similar.
     */
    public static InferenceApplicationResult applyRuleInteractively(String rule, SpiderDiagram diagram) throws RuleApplicationException, TacticApplicationException {
        return applyRuleInteractively(null, InferenceRules.getInferenceRule(rule), null, Goals.createGoalsFrom(diagram));
    }

    public static RuleArg collectArgument(JFrame window, InferenceRule<? extends RuleArg> rule, int subgoalIndex, Goals goals) {
        RuleArg ruleArg;
        RuleApplicationInstruction<? extends RuleArg> instructions = rule.getProvider().getInstructions();

        // Get the inference rule arguments, if the inference rule needs any.
        if (instructions == null) {
            ruleArg = new SubgoalIndexArg(subgoalIndex);
        } else {
            // Ask the user for additional parameters to the inference rule.
            SelectionDialog dsd = new SelectionDialog(window, true, goals.getGoalAt(subgoalIndex), instructions.getSelectionSteps());
            dsd.pack();
            dsd.setVisible(true);

            if (dsd.isCancelled()) {
                throw new RuntimeException("User Cancelled");
            } else {
                ruleArg = instructions.extractRuleArg(dsd.getSelection(), subgoalIndex);
            }
        }

        return ruleArg;
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Stuff">
    /**
     * <p><span style="font-weight:bold">Caveat</span>: exactly one of the
     * arguments 'proof' and 'goals' must be given (i.e. non-{@code null}).
     * Otherwise an exception will be thrown.</p>
     *
     * @param window
     * @param rule
     * @param proof
     * @param goals
     * @return
     * @throws RuleApplicationException
     */
    @SuppressWarnings("unchecked")
    private static InferenceApplicationResult applyRuleInteractively(JFrame window, InferenceRule<? extends RuleArg> rule, Proof proof, Goals goals) throws RuleApplicationException,TacticApplicationException {
        // If the caller provided a proof object, use it to get the last goals
        // from and apply the rule one. Otherwise use the goals.
        // Throw an exception if not exactly one of them is null.
        if (goals == null ^ proof == null) {
            // If the user provided a proof object, we will apply the rule on
            // the pending goals of the proof. So, get the goals from it.
            if (proof != null) {
                goals = proof.getLastGoals();
            }

            // Now check if the goals aren't empty... We cannot apply a rule on
            // empty goals...
            if (goals == null || goals.isEmpty()) {
                throw new RuleApplicationException(speedith.i18n.Translations.i18n("RULE_APP_EMPTY_GOALS"));
            }

            RuleArg ruleArg;
            int subgoalIndex = 0;
            if (goals.getGoalsCount() > 1) {
                try {
                    SelectSubgoalDialog dsd = new SelectSubgoalDialog(window, true, goals);
                    dsd.pack();
                    dsd.setVisible(true);

                    if (dsd.isCancelled()) {
                        throw new RuntimeException("User Cancelled");
                    } else {
                        subgoalIndex = dsd.getSelectedIndex();
                    }

                } catch (RuntimeException e) {
                    return null;
                }
            }

            try {
                ruleArg = collectArgument(window, rule, subgoalIndex, goals);
            } catch (RuntimeException e) {
                return null;
            }

            // Finally, apply the inference rule.
            if (proof != null) {
                return proof.applyRule((Inference<RuleArg, RuleApplicationResult>) rule, ruleArg, RuleApplicationType.INTERACTIVE,"");
            } else {
                return rule.apply(ruleArg, goals);
            }
        } else {
            throw new IllegalArgumentException("Exactly one of 'goals' or 'proof' must be provided (the other must be null).");
        }
    }
    // </editor-fold>
}
