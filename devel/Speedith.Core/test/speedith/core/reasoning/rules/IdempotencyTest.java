/*
 *   Project: Speedith.Core
 * 
 * File name: IdempotencyTest.java
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

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class IdempotencyTest {
    
    public IdempotencyTest() {
    }

    @BeforeClass
    public static void setUpClass() throws Exception {
    }

    @AfterClass
    public static void tearDownClass() throws Exception {
    }
    
    @Before
    public void setUp() {
    }
    
    @After
    public void tearDown() {
    }

    @Test
    public void testApply() throws Exception {
        InferenceRule<? extends RuleArg> rule = InferenceRules.getInferenceRule(Idempotency.InferenceRuleName);
        
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_11);
        int subDiagramIndex = 0;
        SpiderDiagram transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(SpiderDiagrams.createNullSD()));
        
        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7);
        subDiagramIndex = 0;
        transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(SpiderDiagrams.createNullSD()));
        
        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8);
        subDiagramIndex = 0;
        transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(SpiderDiagrams.createNullSD()));
        
        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_12);
        subDiagramIndex = 0;
        transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(SpiderDiagrams.createNullSD()));
        
        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_13);
        subDiagramIndex = 0;
        transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(sd.getSubDiagramAt(2)));
        assertTrue(!transformedSD.equals(sd.getSubDiagramAt(1)));
        assertTrue(transformedSD.equalsSemantically(sd.getSubDiagramAt(2)));
        assertTrue(transformedSD.equalsSemantically(sd.getSubDiagramAt(1)));
        assertTrue(transformedSD != (sd.getSubDiagramAt(1)));
        assertTrue(transformedSD == (sd.getSubDiagramAt(2)));
        
        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_14);
        subDiagramIndex = 0;
        transformedSD = applyRule(rule, subDiagramIndex, sd);
        assertTrue(!sd.equals(transformedSD));
        assertTrue(transformedSD.equals(sd.getSubDiagramAt(2)));
        assertTrue(!transformedSD.equals(sd.getSubDiagramAt(1)));
        assertTrue(transformedSD.equalsSemantically(sd.getSubDiagramAt(2)));
        assertTrue(transformedSD.equalsSemantically(sd.getSubDiagramAt(1)));
        assertTrue(transformedSD != (sd.getSubDiagramAt(1)));
        assertTrue(transformedSD == (sd.getSubDiagramAt(2)));
    }

    private SpiderDiagram applyRule(InferenceRule<? extends RuleArg> rule, final int subDiagramIndex, SpiderDiagram sd) throws RuleApplicationException {
        return rule.apply(new SubDiagramIndexArg(0, subDiagramIndex), Goals.createGoalsFrom(sd)).getGoals().getGoalAt(0);
    }
}
