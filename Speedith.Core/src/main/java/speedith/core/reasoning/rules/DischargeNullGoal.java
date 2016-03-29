
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

import speedith.core.i18n.Translations;
import speedith.core.lang.DiagramType;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;

import java.io.Serializable;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * This inference rule removes a {@link NullSpiderDiagram null-subgoal} from the
 * list of current goals.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class DischargeNullGoal extends SimpleInferenceRule<SubgoalIndexArg> implements BasicInferenceRule<SubgoalIndexArg>, Serializable {

    /**
     * The name of this inference rule.
     * <p>This value is returned by the {@link SimpleInferenceRule#getInferenceName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "discharge_goal";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = -905890625282823817L;

    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        // Check that the arguments to this rule are of the correct type.
        SubgoalIndexArg arg = getTypedRuleArgs(args);
        // Check if the subgoal is a NullSpiderDiagram
        SpiderDiagram targetGoal = getSubgoal(arg, goals);
        if (targetGoal instanceof NullSpiderDiagram) {
            SpiderDiagram[] newSubgoals = getGoalsWithoutSubgoal(goals, arg.getSubgoalIndex());
            return createRuleApplicationResult(newSubgoals);
        } else {
            throw new RuleApplicationException(i18n("RULE_DISCHARGE_NULL_GOAL_NOT_APPLICABLE"));
        }
    }

    private SpiderDiagram[] getGoalsWithoutSubgoal(Goals goals, int subgoalIndex) {
        SpiderDiagram[] newSubgoals = new SpiderDiagram[goals.getGoalsCount() - 1];
        int currentGoalIndex = 0;
        int newGoalsCount = 0;
        for (SpiderDiagram goal : goals.getGoals()) {
            if (currentGoalIndex++ != subgoalIndex) {
                newSubgoals[newGoalsCount++] = goal;
            }
        }
        return newSubgoals;
    }

    @Override
    public DischargeNullGoal getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "DISCHARGE_NULL_GOAL_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return i18n(locale, "DISCHARGE_NULL_GOAL_PRETTY_NAME");
    }

    @Override
    public Class<SubgoalIndexArg> getArgumentType() {
        return SubgoalIndexArg.class;
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    public RuleApplicationInstruction<SubgoalIndexArg> getInstructions() {
        return null;
    }


}
