/*
 *   Project: Speedith.Core
 * 
 * File name: SplitSpiders.java
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
import static speedith.core.i18n.Translations.*;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.reasoning.BasicInferenceRule;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.SpiderZoneArg;

/**
 * The implementation of the 'split spiders' diagrammatic inference rule.
 * <p></p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SplitSpiders implements InferenceRule, BasicInferenceRule {

    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        if (goals == null) {
            throw new RuleApplicationException(i18n("RULE_NO_SUBGOALS"));
        } else if (args instanceof SpiderZoneArg) {
            final SpiderZoneArg arg = (SpiderZoneArg) args;
            // Check that the subgoal actually exists:
            if (arg.getSubgoalIndex() >= goals.getGoalsCount() || arg.getSubgoalIndex() < 0) {
                throw new RuleApplicationException("The chosen subgoal does not exist. Subgoal index out of range.");
            }
            SpiderDiagram sd = goals.getGoalAt(arg.getSubgoalIndex());
            // Get the primary spider diagram at the given index:
            SpiderDiagram newSd = sd.transform(new IdTransformer() {

                @Override
                public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                    if (diagramIndex == arg.getSubDiagramIndex()) {
                        done = true;
                        return SpiderDiagrams.createNullSD();
                    }
                    return null;
                }
            });
            SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
            newSubgoals[arg.getSubgoalIndex()] = newSd;
            return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
        } else {
            throw new RuleApplicationException(i18n("RULE_INVALID_ARGS"));
        }
    }
}
