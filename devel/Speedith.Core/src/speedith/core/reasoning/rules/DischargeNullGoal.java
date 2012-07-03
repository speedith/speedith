
/*
 *   Project: Speedith.Core
 * 
 * File name: DischargeNullGoal.java
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
package speedith.core.reasoning.rules;

import java.util.Locale;
import static speedith.core.i18n.Translations.*;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;

/**
 * This inference rule removes a {@link NullSpiderDiagram null-subgoal} from the
 * list of current goals.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class DischargeNullGoal extends SimpleInferenceRule<SubgoalIndexArg> implements BasicInferenceRule<SubgoalIndexArg> {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule.
     * <p>This value is returned by the {@link SimpleInferenceRule#getInferenceRuleName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "discharge_goal";
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        // Check that the arguments to this rule are of the correct type.
        SubgoalIndexArg arg = getTypedRuleArgs(args);
        // Check if the subgoal is a NullSpiderDiagram
        SpiderDiagram targetGoal = getSubgoal(arg, goals);
        if (targetGoal instanceof NullSpiderDiagram) {
            // This rule changes the number of goals (it reduces it by one--it
            // removes the selected subgoal).
            SpiderDiagram[] newSubgoals = new SpiderDiagram[goals.getGoalsCount() - 1];
            int cursg = 0, sgcount = 0;
            for (SpiderDiagram goal : goals.getGoals()) {
                if (cursg++ != arg.getSubgoalIndex()) {
                    newSubgoals[sgcount++] = goal;
                }
            }
            // Finally return the changed goals.
            return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
        } else {
            throw new RuleApplicationException(i18n("RULE_DISCHARGE_NULL_GOAL_NOT_APPLICABLE"));
        }
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    public DischargeNullGoal getInferenceRule() {
        return this;
    }

    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    public String getDescription(Locale locale) {
        return i18n(locale, "DISCHARGE_NULL_GOAL_DESCRIPTION");
    }

    public String getPrettyName(Locale locale) {
        return i18n(locale, "DISCHARGE_NULL_GOAL_PRETTY_NAME");
    }

    public Class<SubgoalIndexArg> getArgumentType() {
        return SubgoalIndexArg.class;
    }

    public RuleApplicationInstruction<SubgoalIndexArg> getInstructions() {
        return null;
    }
    // </editor-fold>
}
