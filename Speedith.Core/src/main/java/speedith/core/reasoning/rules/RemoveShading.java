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

import speedith.core.i18n.Translations;
import speedith.core.lang.DiagramType;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectSingleZoneInstruction;
import speedith.core.reasoning.rules.transformers.RemoveShadingTransformer;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * Erases shading from a zone.
 *
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
public class RemoveShading extends SimpleInferenceRule<MultipleRuleArgs>
        implements BasicInferenceRule<MultipleRuleArgs>, ForwardRule<MultipleRuleArgs>, Serializable {

    public static final String InferenceRuleName = "Erase Shading";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = -4093837815231375163L;

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return "Erases the shading from a zone.";
    }

    @Override
    public String getPrettyName(Locale locale) {
        return InferenceRuleName;
    }

    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return new SelectSingleZoneInstruction();
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        MultipleRuleArgs ruleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(ruleArgs);
        ArrayList<ZoneArg> zones = getZoneArgsFrom(ruleArgs);
        SubDiagramIndexArg target = getTargetDiagramArg(ruleArgs);
        return apply(target, zones, goals, ApplyStyle.Forward);
    }

    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        MultipleRuleArgs ruleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(ruleArgs);
        ArrayList<ZoneArg> zones = getZoneArgsFrom(ruleArgs);
        SubDiagramIndexArg target = getTargetDiagramArg(ruleArgs);
        return apply(target, zones, goals, ApplyStyle.GoalBased );
    }



    protected RuleApplicationResult apply(SubDiagramIndexArg target, ArrayList<ZoneArg> targetContours, Goals goals, ApplyStyle applyStyle) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        SpiderDiagram targetSubgoal = getSubgoal(target, goals);
        newSubgoals[target.getSubgoalIndex()] = targetSubgoal.transform(new RemoveShadingTransformer(target, targetContours, applyStyle));
        return createRuleApplicationResult(newSubgoals);
    }

    public ArrayList<ZoneArg> getZoneArgsFrom(MultipleRuleArgs args) throws RuleApplicationException {
        MultipleRuleArgs multipleRuleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(multipleRuleArgs);
        ArrayList<ZoneArg> contourArgs = new ArrayList<>();
        int subDiagramIndex = -1;
        int goalIndex = -1;
        for (RuleArg ruleArg : multipleRuleArgs) {
            // an interactive application of IntroContour contains also a SubDiagramIndexArg,
            // to refer to the diagram the rule shall be applied to.
            if (ruleArg instanceof ZoneArg) {
                ZoneArg zoneArg = ZoneArg.getZoneArgFrom(ruleArg);
                subDiagramIndex = ZoneArg.assertSameSubDiagramIndices(subDiagramIndex, zoneArg);
                goalIndex = ZoneArg.assertSameGoalIndices(goalIndex, zoneArg);
                contourArgs.add(zoneArg);
            }
        }
        return contourArgs;
    }

    private SubDiagramIndexArg getTargetDiagramArg(MultipleRuleArgs args) throws RuleApplicationException {
        return (SubDiagramIndexArg) args.get(0);
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

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
