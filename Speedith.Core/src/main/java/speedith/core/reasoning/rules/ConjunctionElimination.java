/*
 *   Project: Speedith.Core
 * 
 * File name: ConjunctionElimination.java
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

import speedith.core.i18n.Translations;
import speedith.core.lang.DiagramType;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.instructions.SelectOperatorAndSubDiagramInstruction;
import speedith.core.reasoning.rules.transformers.ConjunctionEliminationTransformer;

import java.io.Serializable;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ConjunctionElimination extends SimpleInferenceRule<MultipleRuleArgs> implements Serializable, ForwardRule<MultipleRuleArgs>{

    /**
     * The name of this inference rule.
     */
    public static final String InferenceRuleName = "conjunction_elimination";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = -1908339958775714434L;

    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, ApplyStyle.GoalBased);
    }

    private RuleApplicationResult apply(RuleArg args, Goals goals, ApplyStyle applyStyle) throws RuleApplicationException {
        MultipleRuleArgs mult = getTypedRuleArgs(args);
        SubDiagramIndexArg operatorDiagram = (SubDiagramIndexArg) mult.get(0);
        SubDiagramIndexArg targetChild = (SubDiagramIndexArg) mult.get(1);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[operatorDiagram.getSubgoalIndex()] = getSubgoal(operatorDiagram, goals).transform(new ConjunctionEliminationTransformer(operatorDiagram.getSubDiagramIndex(), targetChild, applyStyle));
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public InferenceRule<MultipleRuleArgs> getInferenceRule() {
        return this;
    }
    
    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    public String getDescription(Locale locale) {
        return Translations.i18n(locale, "CONJUNCTION_ELIMINATION_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }
    
    @Override
    public String getPrettyName(Locale locale) {
        return Translations.i18n(locale, "CONJUNCTION_ELIMINATION_PRETTY_NAME");
    }
    
    @Override
    public Class<MultipleRuleArgs> getArgumentType() {
        return MultipleRuleArgs.class;
    }
    
    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return new SelectOperatorAndSubDiagramInstruction();
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, ApplyStyle.Forward);
    }
}
