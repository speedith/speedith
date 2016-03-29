/*
 *   Project: Speedith.Core
 * 
 * File name: RemoveContour.java
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
import speedith.core.reasoning.rules.transformers.RemoveContoursTransformer;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class RemoveContour extends SimpleInferenceRule<MultipleRuleArgs> implements Serializable {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule.
     */
    public static final String InferenceRuleName = "remove_contour";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.SpiderDiagram,DiagramType.EulerDiagram);
    private static final long serialVersionUID = -869717711275052747L;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Inference Rule Implementation">
    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        ArrayList<ContourArg> contourArgs = ContourArg.getContourArgsFrom(getTypedRuleArgs(args));
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[contourArgs.get(0).getSubgoalIndex()] = getSubgoal(contourArgs.get(0), goals).transform(new RemoveContoursTransformer(contourArgs));
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
    public String getDescription(Locale locale) {
        return Translations.i18n(locale, "REMOVE_CONTOUR_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_DIAGRAMMATIC");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return Translations.i18n(locale, "REMOVE_CONTOUR_PRETTY_NAME");
    }

    @Override
    public Class<MultipleRuleArgs> getArgumentType() {
        return MultipleRuleArgs.class;
    }

    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return new SelectContoursInstruction();
    }
    //</editor-fold>


    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
