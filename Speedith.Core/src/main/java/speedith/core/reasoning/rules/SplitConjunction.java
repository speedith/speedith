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

import speedith.core.lang.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction;
import speedith.core.reasoning.rules.transformers.SplitConjunctionTransformer;

import java.io.Serializable;
import java.util.*;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SplitConjunction extends UnaryForwardRule implements Serializable {

    public static final String InferenceRuleName = "Split Conjunction";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.SpiderDiagram, DiagramType.EulerDiagram);
    private static final long serialVersionUID = 5705804693584296643L;

    /*
     * Not used by this implementation! The right transformer is directly created
     * in the method apply(RuleArg, Goals, ApplyStyle)
     */
    @Override
    protected Transformer getSententialTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
        return new IdTransformer();
    }

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return "";
    }

    @Override
    public String getPrettyName(Locale locale) {
        return InferenceRuleName;
    }

    @Override
    public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
        return new SelectSingleOperatorInstruction(Operator.Conjunction);
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    protected RuleApplicationResult apply(final RuleArg args, Goals goals, ApplyStyle applyStyle) throws RuleApplicationException {
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        List<SpiderDiagram> newSubgoals = new LinkedList<>();
        for (int i=0; i< goals.getGoalsCount();i++) {
            if (i == arg.getSubgoalIndex()) {
                SpiderDiagram target = getSubgoal(arg, goals);
                newSubgoals.add(
                        target.transform(new SplitConjunctionTransformer(arg.getSubDiagramIndex(), applyStyle, 0)));
                newSubgoals.add(
                        target.transform(new SplitConjunctionTransformer(arg.getSubDiagramIndex(), applyStyle, 1)));
            } else {
                newSubgoals.add(goals.getGoalAt(i));
            }

        }
//        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
 //       newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(getSententialTransformer(arg, applyStyle));
        return createRuleApplicationResult(newSubgoals.toArray(new SpiderDiagram[goals.getGoalsCount()+1]));
    }

}
