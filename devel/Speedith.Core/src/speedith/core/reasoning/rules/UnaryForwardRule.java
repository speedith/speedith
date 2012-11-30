/*
 *   Project: Speedith.Core
 * 
 * File name: UnaryForwardRule.java
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
package speedith.core.reasoning.rules;

import java.util.ArrayList;
import java.util.Locale;
import speedith.core.i18n.Translations;
import static speedith.core.i18n.Translations.*;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.TransformationException;
import speedith.core.lang.Transformer;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;

/**
 * The base class for all forward inference rules that take one spider diagram
 * and produce an entailed new one.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class UnaryForwardRule
        extends SimpleInferenceRule<SubDiagramIndexArg>
        implements BasicInferenceRule<SubDiagramIndexArg>, ForwardRule<SubDiagramIndexArg> {

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, ApplyStyle.GoalBased);
    }

    protected RuleApplicationResult apply(final RuleArg args, Goals goals, ApplyStyle applyStyle) throws RuleApplicationException {
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(getSententialTransformer(arg));
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Sentential Rule-Specific Stuff">
    protected abstract Transformer getSententialTransformer(SubDiagramIndexArg arg);
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    @Override
    public UnaryForwardRule getInferenceRule() {
        return this;
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }

    @Override
    public Class<SubDiagramIndexArg> getArgumentType() {
        return SubDiagramIndexArg.class;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Forward Rule">
    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, ApplyStyle.Forward);
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    protected static abstract class UnaryForwardTransformer extends IdTransformer {

        private final SubDiagramIndexArg arg;
        private final ApplyStyle applyStyle;

        public UnaryForwardTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
            this.arg = arg;
            this.applyStyle = applyStyle;
        }

        @Override
        public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target diagram.
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // The diagram must appear at a fitting position (depending on the application style):
                if (SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
                    return apply(csd);
                } else {
                    throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"));
                }
            }
            return null;
        }

        @Override
        public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target diagram.
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // The diagram must appear as a positive term:
                if (SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
                    return apply(nsd);
                } else {
                    throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"));
                }
            }
            return null;
        }

        @Override
        public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target diagram.
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // The diagram must appear as a positive term:
                if (SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
                    return apply(psd);
                } else {
                    throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"));
                }
            }
            return null;
        }

        public SubDiagramIndexArg getArg() {
            return arg;
        }

        protected SpiderDiagram apply(CompoundSpiderDiagram sd) {
            return sd;
        }

        protected SpiderDiagram apply(PrimarySpiderDiagram sd) {
            return sd;
        }

        protected SpiderDiagram apply(NullSpiderDiagram sd) {
            return sd;
        }
    }
    //</editor-fold>
}
