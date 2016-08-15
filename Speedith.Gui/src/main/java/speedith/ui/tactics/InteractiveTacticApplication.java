package speedith.ui.tactics;

import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;
import speedith.core.reasoning.tactical.InferenceTactic;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.core.reasoning.tactical.TacticApplicationResult;
import speedith.ui.selection.SelectSubgoalDialog;

import javax.swing.*;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public final class InteractiveTacticApplication {

    private InteractiveTacticApplication() {}

    public static boolean applyTacticInteractively(JFrame window, InferenceTactic<? extends RuleArg> rule, int subgoalIndex, Proof proof) throws RuleApplicationException,TacticApplicationException {
        return applyTacticInteractively(window, rule, proof, null) != null;
    }

    /**
     * <p><span style="font-weight:bold">Caveat</span>: exactly one of the
     * arguments 'proof' and 'goals' must be given (i.e. non-{@code null}).
     * Otherwise an exception will be thrown.</p>
     *
     * @param window
     * @param rule
     *
     * @param proof
     * @param goals
     * @return
     * @throws RuleApplicationException
     */
    @SuppressWarnings("unchecked")
    private static InferenceApplicationResult applyTacticInteractively(JFrame window, InferenceTactic<? extends RuleArg> rule, Proof proof, Goals goals) throws RuleApplicationException,TacticApplicationException {
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
            // if there is more than one current subgoal, let
            // the user select the subgoal the tactic should work on
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
            ruleArg = new SubgoalIndexArg(subgoalIndex);
            // Finally, apply the inference .
            if (proof != null) {
                return proof.applyRule((Inference<RuleArg, TacticApplicationResult>) rule, ruleArg, RuleApplicationType.TACTIC,"");
            } else {
                return rule.apply(ruleArg, goals);
            }
        } else {
            throw new IllegalArgumentException("Exactly one of 'goals' or 'proof' must be provided (the other must be null).");
        }
    }
}
