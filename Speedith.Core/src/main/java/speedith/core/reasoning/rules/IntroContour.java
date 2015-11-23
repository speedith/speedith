/*
 *   Project: Speedith.Core
 * 
 * File name: GeneralTautology.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2013 Matej Urbas
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

import java.util.*;

import speedith.core.i18n.Translations;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.instructions.SelectSingleSubDiagramAndContourInstruction;
import speedith.core.reasoning.rules.transformers.IntroduceContoursTransformer;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class IntroContour extends SimpleInferenceRule<MultipleRuleArgs>
        implements BasicInferenceRule<MultipleRuleArgs>, ForwardRule<MultipleRuleArgs> {

    public static final String InferenceRuleName = "Introduce Contour";

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
//        throw new RuleApplicationException("Not implemented yet!");
        //return null;
    }

    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        MultipleRuleArgs ruleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(ruleArgs);
        SubDiagramIndexArg target = getTargetDiagramArg(ruleArgs);
        ArrayList<ContourArg> contours = getContourArgsFrom(ruleArgs);
        return apply(target, contours, goals);
    }

    private SubDiagramIndexArg getTargetDiagramArg(MultipleRuleArgs args) throws RuleApplicationException {
        return (SubDiagramIndexArg) args.get(0);
    }

    private ArrayList<ContourArg> getContourArgsFrom(MultipleRuleArgs args) throws RuleApplicationException {
        ArrayList<ContourArg> contourArgs = new ArrayList<>();
        int subDiagramIndex = -1;
        int goalIndex = -1;
        for (RuleArg ruleArg : args) {
            if (ruleArg instanceof ContourArg) {
                ContourArg contourArg = ContourArg.getContourArgFrom(ruleArg);
                subDiagramIndex = ContourArg.assertSameSubDiagramIndices(subDiagramIndex, contourArg);
                goalIndex = ContourArg.assertSameGoalIndices(goalIndex, contourArg);
                contourArgs.add(contourArg);
            }
        }
        return contourArgs;
    }

    private RuleApplicationResult apply(SubDiagramIndexArg target, ArrayList<ContourArg> targetContours, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        SpiderDiagram targetSubgoal = getSubgoal(target, goals);
        newSubgoals[target.getSubgoalIndex()] = targetSubgoal.transform(new IntroduceContoursTransformer(target, targetContours));
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public InferenceRule<MultipleRuleArgs> getInferenceRule() {
        return this;
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_DIAGRAMMATIC");
    }

    @Override
    public Class<MultipleRuleArgs> getArgumentType() {
        return MultipleRuleArgs.class;
    }

    /*    @Override
            protected Transformer getSententialTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
                return new IdTransformer();
            }
        */
    @Override
    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return "Introduces new contours into a diagram.";
    }

    @Override
    public String getPrettyName(Locale locale) {
        return InferenceRuleName;
    }

    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return new SelectSingleSubDiagramAndContourInstruction();
    }
}
