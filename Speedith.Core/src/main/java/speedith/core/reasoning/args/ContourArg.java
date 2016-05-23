/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderArg.java
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
package speedith.core.reasoning.args;

import speedith.core.reasoning.RuleApplicationException;

import java.io.Serializable;
import java.util.ArrayList;

/**
 * Contains the name of the contour that should be passed to an inference rule.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ContourArg extends SubDiagramIndexArg implements Serializable {

    private static final long serialVersionUID = 4883774230687002322L;
    private final String contour;

    /**
     * Initialises an argument object for a spider-diagrammatic inference rule.
     *
     * @param subgoalIndex the index of the subgoal to target by the rule.
     * @param primarySDIndex the index of the sub-diagram to target by the rule.
     * @param contour the name of the contour that should be passed to an
     * inference rule. This parameter must not be
     * {@code null} or empty, otherwise an exception will be thrown.
     */
    public ContourArg(int subgoalIndex, int primarySDIndex, String contour) {
        super(subgoalIndex, primarySDIndex);
        if (contour == null || contour.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "contour"));
        }
        this.contour = contour;
    }

    /**
     * The name of the contour that should be passed to an inference rule.
     * <p>This property is guaranteed to return a non-null and non-empty
     * string.</p>
     *
     * @return name of the spider that should be passed to an inference rule.
     */
    public String getContour() {
        return contour;
    }

    public static int assertSameSubDiagramIndices(int previousSubDiagramIndex, ContourArg contourArg) throws RuleApplicationException {
        if (previousSubDiagramIndex != -1 && previousSubDiagramIndex != contourArg.getSubDiagramIndex()) {
            throw new RuleApplicationException("The contours must be from the same unitary spider diagram.");
        } else {
            previousSubDiagramIndex = contourArg.getSubDiagramIndex();
        }
        return previousSubDiagramIndex;
    }

    public static ContourArg getContourArgFrom(RuleArg ruleArg) throws RuleApplicationException {
        if (!(ruleArg instanceof ContourArg)) {
            throw new RuleApplicationException("The copy contours rule takes only contours as arguments.");
        }
        return (ContourArg)ruleArg;
    }

    public static ArrayList<ContourArg> getContourArgsFrom(MultipleRuleArgs multipleRuleArgs) throws RuleApplicationException {
        ArrayList<ContourArg> contourArgs = new ArrayList<>();
        int subDiagramIndex = -1;
        int goalIndex = -1;
        for (RuleArg ruleArg : multipleRuleArgs) {
            ContourArg contourArg = getContourArgFrom(ruleArg);
            subDiagramIndex = assertSameSubDiagramIndices(subDiagramIndex, contourArg);
            goalIndex = assertSameGoalIndices(goalIndex, contourArg);
            contourArgs.add(contourArg);
        }
        return contourArgs;
    }
}
