/*
 *   Project: Speedith.Core
 * 
 * File name: ImplicationTautology.java
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
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.TransformationException;
import speedith.core.reasoning.BasicInferenceRule;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import static speedith.core.i18n.Translations.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction;

/**
 * The implementation of the <span style="font-weight:bold">implication
 * tautology</span> inference rule. <p>This inference rule takes a sub-diagram
 * of the form <span style="font-style:italic;">φ &#x27f6; φ</span> and converts
 * it to a {@link NullSpiderDiagram null diagram}.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ImplicationTautology extends SimpleInferenceRule<SubDiagramIndexArg> implements BasicInferenceRule<SubDiagramIndexArg>, ForwardRule<SubDiagramIndexArg> {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule. <p>This value is returned by the {@link ImplicationTautology#getInferenceRuleName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "implication_tautology";
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        // Check that the arguments to this rule are of the correct type.
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        // This rule does not change the number of goals (it simply rewrites
        // sub-formulae to null diagrams).
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        // Now apply the rewrite on the chosen subgoal.
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new IdempotencyTransformer(arg), false);
        // Finally return the changed goals.
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Forward Rule">
    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    @Override
    public ImplicationTautology getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "IMPLICATION_TAUTOLOGY_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return i18n(locale, "IMPLICATION_TAUTOLOGY_PRETTY_NAME");
    }

    @Override
    public Class<SubDiagramIndexArg> getArgumentType() {
        return SubDiagramIndexArg.class;
    }

    @Override
    public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
        return SingletonContainer.Instruction;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private  static final class SingletonContainer {
        private static final SelectSingleOperatorInstruction Instruction = new SelectSingleOperatorInstruction(Operator.Implication, Operator.Equivalence);
    }

    private class IdempotencyTransformer extends IdTransformer {

        private final SubDiagramIndexArg arg;

        public IdempotencyTransformer(SubDiagramIndexArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target sub-diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // The compound diagram must be an implication:
                if (Operator.Implication.equals(csd.getOperator())) {
                    if (csd.getOperand(0).isSEquivalentTo(csd.getOperand(1))) {
                        return SpiderDiagrams.createNullSD();
                    } else {
                        throw new TransformationException(i18n("RULE_IMPLICATION_TAUTOLOGY_NOT_APPLICABLE_SEM"));
                    }
                } else {
                    throw new TransformationException(i18n("RULE_IMPLICATION_TAUTOLOGY_NOT_APPLICABLE"));
                }
            }
            return null;
        }
    }
    //</editor-fold>
}
