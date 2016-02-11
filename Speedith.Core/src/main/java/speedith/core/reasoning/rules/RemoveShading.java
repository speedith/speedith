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
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectSingleZoneInstruction;
import speedith.core.reasoning.rules.transformers.RemoveShadingTransformer;

import java.io.Serializable;
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
public class RemoveShading extends SimpleInferenceRule<ZoneArg>
        implements BasicInferenceRule<ZoneArg>, ForwardRule<ZoneArg>, Serializable {

    public static final String InferenceRuleName = "Erase Shading";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram);
    private static final long serialVersionUID = -4093837815231375163L;

    @Override
    public String getInferenceRuleName() {
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
    public RuleApplicationInstruction<ZoneArg> getInstructions() {
        return new SelectSingleZoneInstruction();
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }

    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        ZoneArg subgoal = (ZoneArg) args;
        SpiderDiagram targetSubgoal = getSubgoal(subgoal, goals);
        newSubgoals[subgoal.getSubgoalIndex()] = targetSubgoal.transform(new RemoveShadingTransformer(subgoal));
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public InferenceRule<ZoneArg> getInferenceRule() {
        return this;
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_DIAGRAMMATIC");
    }

    @Override
    public Class<ZoneArg> getArgumentType() {
        return ZoneArg.class;
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
