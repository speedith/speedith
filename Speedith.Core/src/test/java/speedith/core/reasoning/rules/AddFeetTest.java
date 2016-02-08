/*
 *   Project: Speedith.Core
 * 
 * File name: AddFeetTest.java
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

import org.junit.Test;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.SpiderRegionArg;

import static org.junit.Assert.assertSame;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class AddFeetTest {
    
    public AddFeetTest() {
    }

    @Test
    public void testApplyForward() throws ReadingException, RuleApplicationException {
        AddFeet addFeet = (AddFeet) InferenceRules.getInferenceRule(AddFeet.InferenceRuleName);
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_17);
        RuleApplicationResult result = addFeet.applyForwards(new SpiderRegionArg(0, 0, "s1", new Region(new Zone("A", "B"))), Goals.createGoalsFrom(sd));
        SpiderDiagram expectedResult = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_19);
        assertSame(expectedResult, result.getGoals().getGoalAt(0));
    }
}
