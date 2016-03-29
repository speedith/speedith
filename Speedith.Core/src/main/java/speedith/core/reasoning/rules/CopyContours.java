/*
 *   Project: Speedith.Core
 * 
 * File name: CopyContour.java
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
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.rules.instructions.SelectContoursInstruction;
import speedith.core.reasoning.rules.transformers.CopyContoursTransformer;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CopyContours extends SimpleInferenceRule<MultipleRuleArgs> implements Serializable {

    /**
     * The name of this inference rule.
     */
    public static final String InferenceRuleName = "copy_contours";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = -3569161621056814002L;


    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(getContourArgsFrom(args), goals);
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
    public String getDescription(Locale locale) {
        return Translations.i18n(locale, "COPY_CONTOURS_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return Translations.i18n(locale, "COPY_CONTOURS_PRETTY_NAME");
    }

    @Override
    public Class<MultipleRuleArgs> getArgumentType() {
        return MultipleRuleArgs.class;
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return new SelectContoursInstruction();
    }

    private ArrayList<ContourArg> getContourArgsFrom(RuleArg args) throws RuleApplicationException {
        MultipleRuleArgs multipleRuleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(multipleRuleArgs);
        return ContourArg.getContourArgsFrom(multipleRuleArgs);
    }

    private RuleApplicationResult apply(ArrayList<ContourArg> targetContours, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        ContourArg inferenceTarget = targetContours.get(0);
        SpiderDiagram targetSubgoal = getSubgoal(inferenceTarget, goals);
        int indexOfParent = targetSubgoal.getParentIndexOf(inferenceTarget.getSubDiagramIndex());
        newSubgoals[inferenceTarget.getSubgoalIndex()] = targetSubgoal.transform(new CopyContoursTransformer(indexOfParent, targetContours));
        return createRuleApplicationResult(newSubgoals);
    }
}
