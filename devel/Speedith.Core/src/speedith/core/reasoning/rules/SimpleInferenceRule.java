/*
 *   Project: Speedith.Core
 * 
 * File name: SimpleInferenceRule.java
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

import java.util.ArrayList;
import java.util.Locale;
import speedith.core.i18n.Translations;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;

/**
 * This simple abstract class provides some helper methods commonly used in
 * inference rules. For example
 * @param <TArgs> the type of arguments the provided inference rule expects. Use
 * the type {@link RuleArg} to specify that the inference rule does not expect
 * any specific arguments.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SimpleInferenceRule<TArgs extends RuleArg> implements InferenceRule<TArgs>, InferenceRuleProvider<TArgs> {

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    @Override
    public String getDescription() {
        return getDescription(Locale.getDefault());
    }

    @Override
    public String getPrettyName() {
        return getPrettyName(Locale.getDefault());
    }

    @Override
    public String toString() {
        return getPrettyName();
    }

    /**
     * This is the default implementation of the {@link InferenceRuleProvider#getInferenceRuleType()}.
     * It returns {@code this.getClass()}.
     * 
     * @return {@code this.getClass()}.
     */
    @SuppressWarnings("unchecked")
    @Override
    public Class<? extends InferenceRule<TArgs>> getInferenceRuleType() {
        return (Class<? extends InferenceRule<TArgs>>) getClass();
    }

    @Override
    public boolean isForwardRule() {
        return ForwardRule.class.isAssignableFrom(getInferenceRuleType());
    }

    @Override
    public boolean isBackwardRule() {
        return BackwardRule.class.isAssignableFrom(getInferenceRuleType());
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    public InferenceRuleProvider<TArgs> getProvider() {
        return this;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Protected Helper Methods">
    /**
     * This method checks if the given arguments are of the type expected by
     * this inference rule (the expected type is provided by the {@link
     * InferenceRuleProvider#getArgumentType()} method).
     * <p>If the expected type is not given or is {@link RuleArg} then this
     * method simply returns {@code null}.</p>
     * <p>If, however, the {@link SimpleInferenceRule#getArgumentType() expected
     * type} is a proper sub-type of {@link RuleArg}, then this method will
     * check whether the given argument is of that type and cast it too. In this
     * case the returned value will be non-{@code null}.</p>
     * @param args the arguments to check for type.
     * @return the arguments cast to the expected type (may be {@code null}, but
     * only if the inference rule does not expect any arguments).
     * @throws RuleApplicationException if the argument does not conform the
     * expected type.
     */
    protected TArgs getTypedRuleArgs(RuleArg args) throws RuleApplicationException {
        Class<TArgs> argType = getArgumentType();
        if (argType == null || argType == RuleArg.class) {
            return null;
        } else if (args == null) {
            throw new RuleApplicationException(i18n("RULE_NO_SUBGOALS"));
        } else if (argType.isInstance(args)) {
            return argType.cast(args);
        } else {
            throw new RuleApplicationException(i18n("RULE_INVALID_ARGS"));
        }
    }

    /**
     * This method returns the subgoal at the given index.
     * @param args the subgoal index arguments.
     * @param goals the goals from which to get the one at the given index.
     * @return a non-{@code null} spider diagram (the subgoal at the given
     * index).
     * <p><span style="font-weight:bold">Note</span>: it is guaranteed that the
     * returned spider diagram will be non-{@code null} (if no exception is
     * thrown).</p>
     * @throws RuleApplicationException this exception is thrown if one of the
     * following occurs:
     *  <ul>
     *      <li>the given arguments are {@code null} or not of type {@link 
     *          SubgoalIndexArg},</li>
     *      <li>the given arguments are not of the type given in the parameter
     *          {@code expectedArgsType},</li>
     *      <li>the index is out of range, or</li>
     *      <li>the subgoal at the given index is {@code null}.</li>
     *  </ul>
     */
    protected static SpiderDiagram getSubgoal(SubgoalIndexArg args, Goals goals) throws RuleApplicationException {
        if (goals == null) {
            throw new RuleApplicationException(i18n("RULE_NO_SUBGOALS"));
        } else if (args == null) {
            throw new RuleApplicationException(i18n("RULE_INVALID_ARGS"));
        } else {
            // Check that the subgoal actually exists:
            if (args.getSubgoalIndex() >= goals.getGoalsCount() || args.getSubgoalIndex() < 0) {
                throw new RuleApplicationException(i18n("RULE_SUBGOAL_INDEX_OUT_OF_RANGE", args.getSubgoalIndex()));
            }
            SpiderDiagram sd = goals.getGoalAt(args.getSubgoalIndex());
            if (sd == null) {
                throw new RuleApplicationException(i18n("RULE_NO_SUBGOAL_AT_INDEX"));
            }
            return sd;
        }
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Helper Methods (public static)">
    public static boolean isForwardApplicable(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int childIndex) {
        if (parents == null) {
            throw new IllegalArgumentException(Translations.i18n("RULE_PARENTS_NEEDED_FOR_FORWARD_CHECK"));
        }
        
        // There must be an implication on the toplevel.
        if (parents.size() < 1) {
            return false;
        }

        // Check that there is really an implication on the toplevel:
        if (!Operator.Implication.equals(parents.get(0).getOperator())) {
            return false;
        }

        // If there is only one parent then this diagram should be the direct
        // left child of the toplevel implication.
        if (parents.size() == 1) {
            return childIndex == 0;
        } else if (childIndices.get(1) != 0) {
            return false;
        }

        // There are some more parents. They all must be conjunctions and
        // disjunctions:
        for (int i = parents.size() - 1; i > 0; --i) {
            Operator parentOperator = parents.get(i).getOperator();
            if (!Operator.Conjunction.equals(parentOperator) || !Operator.Disjunction.equals(parentOperator)) {
                return false;
            }
        }

        // Seems like all requirements are satisfied. This diagram can be
        // applied forward style.
        return true;
    }

    public static boolean isBackwardApplicable(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int childIndex) {
        if (parents == null) {
            throw new IllegalArgumentException(Translations.i18n("RULE_PARENTS_NEEDED_FOR_BACKWARD_CHECK"));
        }
        
        // If this spider diagram is toplevel, it can be applied backwards on:
        if (parents.size() < 1) {
            return true;
        }
        
        // If there is an implication at the toplevel, we should be in its right
        // side:
        int checkDisjConjParentsFrom = 0;
        if (Operator.Implication.equals(parents.get(0).getOperator())) {
            if (parents.size() == 1) {
                return childIndex == 1;
            } else if (childIndices.get(1) != 1) {
                return false;
            }
            // Okay, we are in the RHS of an implication. This means that all
            // other nested parents must be disjunctions and conjunctions
            checkDisjConjParentsFrom = 1;
        }

        // There are some more parents. They all must be conjunctions and
        // disjunctions:
        for (int i = parents.size() - 1; i >= checkDisjConjParentsFrom; --i) {
            Operator parentOperator = parents.get(i).getOperator();
            if (!Operator.Conjunction.equals(parentOperator) || !Operator.Disjunction.equals(parentOperator)) {
                return false;
            }
        }

        // Seems like all requirements are satisfied. This diagram can be
        // applied backward style.
        return true;
    }
    // </editor-fold>
}
