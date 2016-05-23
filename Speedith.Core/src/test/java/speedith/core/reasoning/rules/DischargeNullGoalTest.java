/*
 *   Project: Speedith.Core
 * 
 * File name: DischargeNullGoalTest.java
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

import org.junit.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubgoalIndexArg;

import java.util.Locale;

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class DischargeNullGoalTest {
    
    public DischargeNullGoalTest() {
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
        SpiderDiagram sd1 = SpiderDiagrams.createNullSD();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(GoalsTest.getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_2.sd"));
        SpiderDiagram sd3 = SpiderDiagrams.createNullSD();
        Goals initialGoals = Goals.createGoalsFrom(sd1, sd2, sd3);
        InferenceRule<? extends RuleArg> dischargeGoalRule = InferenceRules.getInferenceRule(DischargeNullGoal.InferenceRuleName);
        SubgoalIndexArg args = new SubgoalIndexArg(0);
        
        RuleApplicationResult appResult = dischargeGoalRule.apply(args, initialGoals);
        Goals newGoals = appResult.getGoals();
        assertEquals(2, newGoals.getGoalsCount());
        assertEquals(initialGoals.getGoalAt(1), newGoals.getGoalAt(0));
        assertSame(initialGoals.getGoalAt(1), newGoals.getGoalAt(0));
        assertEquals(initialGoals.getGoalAt(2), newGoals.getGoalAt(1));
        assertSame(initialGoals.getGoalAt(2), newGoals.getGoalAt(1));
        assertEquals(SpiderDiagrams.createNullSD(), newGoals.getGoalAt(1));
        assertSame(SpiderDiagrams.createNullSD(), newGoals.getGoalAt(1));
        
        args = new SubgoalIndexArg(1);
        appResult = dischargeGoalRule.apply(args, newGoals);
        newGoals = appResult.getGoals();
        assertEquals(1, newGoals.getGoalsCount());
        assertEquals(initialGoals.getGoalAt(1), newGoals.getGoalAt(0));
        assertSame(initialGoals.getGoalAt(1), newGoals.getGoalAt(0));
        
        try {
            args = new SubgoalIndexArg(0);
            appResult = dischargeGoalRule.apply(args, newGoals);
            assertTrue("An exception should have been thrown.", false);
        } catch (RuleApplicationException rae) {
            assertNotNull(rae);
        }
    }

    @Test
    public void testGetInferenceRule() {
        DischargeNullGoal instance = new DischargeNullGoal();
        DischargeNullGoal result = instance.getInferenceRule();
        assertEquals(instance, result);
    }

    @Test
    public void testGetInferenceRuleName() {
        DischargeNullGoal instance = new DischargeNullGoal();
        String expResult = DischargeNullGoal.InferenceRuleName;
        String result = instance.getInferenceName();
        assertEquals(expResult, result);
    }

    @Test
    public void testGetDescription() {
        Locale locale = null;
        DischargeNullGoal instance = new DischargeNullGoal();
        String result = instance.getDescription(locale);
        assertNotNull(result);
    }

    @Test
    public void testGetArgumentType() {
        DischargeNullGoal instance = new DischargeNullGoal();
        Class expResult = SubgoalIndexArg.class;
        Class result = instance.getArgumentType();
        assertEquals(expResult, result);
    }
}
