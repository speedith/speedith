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

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;

import java.util.ArrayList;
import java.util.Locale;

import static speedith.core.i18n.Translations.i18n;

/**
 * This simple abstract class provides some helper methods commonly used in
 * inference rules.
 *
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
    public String getCategory() {
        return getCategory(Locale.getDefault());
    }

    @Override
    public String toString() {
        return getPrettyName();
    }

    /**
     * This is the default implementation of the
     * {@link InferenceRuleProvider#getInferenceRuleType()}. It returns
     * {@code this.getClass()}.
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
        return isForwardRule(this);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    @Override
    public InferenceRuleProvider<TArgs> getProvider() {
        return this;
    }

    public static RuleApplicationResult createRuleApplicationResult(SpiderDiagram[] newSubgoals) {
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Protected Helper Methods">
    /**
     * This method checks if the given arguments are of the type expected by
     * this inference rule (the expected type is provided by the {@link
     * InferenceRuleProvider#getArgumentType()} method). <p>If the expected type
     * is not given or is {@link RuleArg} then this method simply returns
     * {@code null}.</p> <p>If, however, the {@link SimpleInferenceRule#getArgumentType() expected
     * type} is a proper sub-type of {@link RuleArg}, then this method will
     * check whether the given argument is of that type and cast it too. In this
     * case the returned value will be non-{@code null}.</p>
     *
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
     *
     * @param args the subgoal index arguments.
     * @param goals the goals from which to get the one at the given index.
     * @return a non-{@code null} spider diagram (the subgoal at the given
     * index). <p><span style="font-weight:bold">Note</span>: it is guaranteed
     * that the returned spider diagram will be non-{@code null} (if no
     * exception is thrown).</p>
     * @throws RuleApplicationException this exception is thrown if one of the
     * following occurs: <ul> <li>the given arguments are {@code null} or not of
     * type {@link
     *          SubgoalIndexArg},</li> <li>the given arguments are not of the type given
     * in the parameter {@code expectedArgsType},</li> <li>the index is out of
     * range, or</li> <li>the subgoal at the given index is {@code null}.</li>
     * </ul>
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
    /**
     * See {@link InferenceRuleProvider#isForwardRule() }
     */
    public static boolean isForwardRule(Class<? extends InferenceRule<?>> infRuleType) {
        return ForwardRule.class.isAssignableFrom(infRuleType);
    }

    /**
     * See {@link InferenceRuleProvider#isForwardRule() }
     */
    public static boolean isForwardRule(InferenceRuleProvider<?> infRuleProvider) {
        return isForwardRule(infRuleProvider.getInferenceRuleType());
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code -1}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static boolean isAtPositivePosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return getPositionType(parents, childIndices, -1, parents == null ? 0 : parents.size()) == PositivePosition;
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code sourceParent}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static boolean isAtPositivePosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int sourceParent) {
        return getPositionType(parents, childIndices, sourceParent, parents == null ? 0 : parents.size()) == PositivePosition;
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code -1}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static boolean isAtNegativePosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return getPositionType(parents, childIndices, -1, parents == null ? 0 : parents.size()) == NegativePosition;
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code sourceParent}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static boolean isAtNegativePosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int sourceParent) {
        return getPositionType(parents, childIndices, sourceParent, parents == null ? 0 : parents.size()) == NegativePosition;
    }

    /**
     * Indicates whether the current subdiagram appears at the right position to
     * be a target of an inference rule application.
     *
     * @return a flag that indicates whether the current subdiagram appears at
     * the right position to be a target of an inference rule application.
     */
    public static boolean isAtFittingPosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ApplyStyle applyStyle, boolean isForwardRule) {
        return isAtFittingPosition(parents, childIndices, -1, applyStyle, isForwardRule);
    }

    /**
     * Indicates whether the current subdiagram appears at the right position to
     * be a target of an inference rule application.
     *
     * @return a flag that indicates whether the current subdiagram appears at
     * the right position to be a target of an inference rule application.
     */
    public static boolean isAtFittingPosition(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int sourceParent, ApplyStyle applyStyle, boolean isForwardRule) {
        int positionType = getPositionType(parents, childIndices, sourceParent);
        if (isForwardRule) {
            if (applyStyle == ApplyStyle.Forward) {
                return positionType == PositivePosition;
            } else {
                return positionType == NegativePosition;
            }
        } else {
            if (applyStyle == ApplyStyle.Forward) {
                return positionType == NegativePosition;
            } else {
                return positionType == PositivePosition;
            }
        }
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code sourceParent}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static int getPositionType(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int sourceParent) {
        return getPositionType(parents, childIndices, sourceParent, parents == null ? 0 : parents.size());
    }

    /**
     * <p>This method calls the {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * method with the following arguments:
     *
     * <ul>
     *
     * <li>{@code parents},</li>
     *
     * <li>{@code childIndices},</li>
     *
     * <li>{@code -1}, and</li>
     *
     * <li>{@code parents.size()}.</li>
     *
     * </ul></p>
     *
     * <p>See {@link SimpleInferenceRule#getPositionType(java.util.ArrayList, java.util.ArrayList, int, int)
     * }
     * for more info.</p>
     */
    public static int getPositionType(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return getPositionType(parents, childIndices, -1, parents == null ? 0 : parents.size());
    }
    public static final int PositivePosition = 0x1;
    public static final int NegativePosition = 0x2;
    public static final int EquivalencePosition = PositivePosition & NegativePosition;

    /**
     * This method gets the position type of the target child as it appears
     * within the source parent. For example, if we have <span
     * style="font-style:italic;">A ⇒ B</span> then <span
     * style="font-style:italic;">A</span> appears positively within the
     * left-hand side of the implication (that is, it appears positively
     * relative to parent {@code 0}), however, <span
     * style="font-style:italic;">A</span> appears negatively within relative to
     * the whole formula (that is, relative to the parent {@code -1}).
     *
     * <p>The list of position types:
     *
     * <ul>
     *
     * <li>{@link SimpleInferenceRule#PositivePosition},</li>
     *
     * <li>{@link SimpleInferenceRule#NegativePosition}, and</li>
     *
     * <li>{@link SimpleInferenceRule#EquivalencePosition}.</li>
     *
     * </ul>
     *
     * </p>
     *
     * @param parents the stack of parents (each parent is a child of the parent
     * at the previous position in this list).
     *
     * @param childIndices contains the child indices for the current diagram
     * (not present in the {@code parents} list) as well as each parent in the
     * {@code parents} list (except for the first one). The value
     * {@code childIndices.get(i)} is the operand index at which parent
     * {@code i + 1} appears within the parent {@code i}. The last value in this
     * list is the operand index of the current spider diagram within the last
     * parent.
     *
     * @param sourceParent from {@code -1} to {@code parents.size() - 1}.
     * Indicates which parent should be taken as the topmost one (relative to
     * which the position type is being determined). {@code -1} indicates that
     * the context just above the first parent should be the relative search
     * point (that is, we are interested in the position type of the target
     * child relative to the whole formula). {@code 0} indicates that we are
     * interested in the position type of the target child relative to the first
     * parent. For example, if we have <span style="font-style:italic;">A ⇒
     * B</span> then <span style="font-style:italic;">A</span> appears
     * positively within parent {@code 0} (that is, within the implication),
     * however, <span style="font-style:italic;">A</span> appears negatively
     * within parent {@code -1} (the whole formula).
     *
     * @param targetChild the level of the child for which we are interested in
     * its position type (can be any value from {@code 0} to
     * {@code parents.size()} (both bounds inclusive).
     *
     * @return one of the position types:
     *
     * <ul>
     *
     * <li>{@link SimpleInferenceRule#PositivePosition},</li>
     *
     * <li>{@link SimpleInferenceRule#NegativePosition}, and</li>
     *
     * <li>{@link SimpleInferenceRule#EquivalencePosition}.</li>
     *
     * </ul>
     */
    public static int getPositionType(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, int sourceParent, int targetChild) {
        // If both `parents` and `childIndices` are `null` we assume that the
        // target diagram has no parents:
        int numOfIndices = childIndices == null ? 0 : childIndices.size();
        int numOfParents = parents == null ? 0 : parents.size();
        if (numOfIndices != numOfParents) {
            throw new IllegalArgumentException();
        }
        // Check that the check bounds are valid:
        // 1.) the 'targetChild' must be within the 'sourceParent'
        if (sourceParent >= targetChild) {
            throw new IllegalArgumentException();
        }
        // 2.) none of the indices must be out of bounds:
        if (sourceParent < -1) {
            throw new IndexOutOfBoundsException();
        }
        if (targetChild < 0 || targetChild > numOfParents || targetChild > numOfIndices) {
            throw new IndexOutOfBoundsException();
        }

        // Now go through all the parents and find out the position type.
        boolean posType = true;
        for (int curParent = sourceParent + 1; curParent < targetChild; curParent++) {
            CompoundSpiderDiagram parent = parents.get(curParent);
            switch (parent.getOperator()) {
                case Negation:
                    posType = !posType;
                    break;
                case Conjunction:
                    break;
                case Disjunction:
                    break;
                case Implication:
                    if (childIndices.get(curParent) == 0) {
                        posType = !posType;
                    }
                    break;
                case Equivalence:
                    return EquivalencePosition;
                default:
                    throw new AssertionError();
            }
        }
        return posType ? PositivePosition : NegativePosition;
    }
    // </editor-fold>
}
