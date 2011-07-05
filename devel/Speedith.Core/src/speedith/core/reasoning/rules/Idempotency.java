/*
 *   Project: Speedith.Core
 * 
 * File name: Idempotency.java
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

import java.util.LinkedList;
import java.util.Locale;
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

/**
 * The implementation of the idempotency inference rule.
 * <p>This inference rule checks whether a {@link CompoundSpiderDiagram binary
 * compound spider diagram} can be reduced to either one of its operands (in case
 * of the {@link Operator#OP_NAME_AND and} or {@link Operator#OP_NAME_OR or}
 * operators), or to the {@link NullSpiderDiagram null diagram} (in case of the
 * {@link Operator#OP_NAME_IMP implies} or {@link Operator#OP_NAME_EQ
 * equivalence} operators).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Idempotency extends SimpleInferenceRule<SubDiagramIndexArg> implements BasicInferenceRule {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule.
     * <p>This value is returned by the {@link Idempotency#getInferenceRuleName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "idempotency";
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new IdempotencyTransformer(arg), false);
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    public Idempotency getInferenceRule() {
        return this;
    }

    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    public String getDescription(Locale locale) {
        return i18n(locale, "SPLIT_SPIDERS_DESCRIPTION");
    }

    public Class<SubDiagramIndexArg> getArgumentType() {
        return SubDiagramIndexArg.class;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private class IdempotencyTransformer extends IdTransformer {

        private final SubDiagramIndexArg arg;

        public IdempotencyTransformer(SubDiagramIndexArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
            // Transform only the target diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // Is the compound diagram a conjunction or a disjunction?
                // Is it an implication or an equivalence?
                if (Operator.getAnd().equals(csd.getOperator()) || Operator.getOr().equals(csd.getOperator())) {
                    if (csd.getOperand(0).equalsSemantically(csd.getOperand(1))) {
                        return csd.getOperand(1);
                    }
                } else if (Operator.getEquivalent().equals(csd.getOperator()) || Operator.getImplies().equals(csd.getOperator())) {
                    if (csd.getOperand(0).equalsSemantically(csd.getOperand(1))) {
                        return SpiderDiagrams.createNullSD();
                    }
                }
                throw new TransformationException(i18n("RULE_IDEMPOTENCY_NOT_APPLICABLE"));
            }
            return null;
        }
    }
    //</editor-fold>
}
