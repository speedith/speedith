/*
 *   Project: Speedith
 * 
 * File name: OperatorLabelTest.java
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
package speedith.draw;

import org.junit.*;
import speedith.core.lang.Operator;
import speedith.ui.OperatorPanel;

import static org.junit.Assert.assertEquals;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class OperatorLabelTest {
    
    public OperatorLabelTest() {
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

    /**
     * Test of getOperator method, of class OperatorPanel.
     */
    @Test
    public void testGetOperator() {
        OperatorPanel instance = new OperatorPanel();
        Operator expResult = null;
        Operator result = instance.getOperator();
        assertEquals(expResult, result);
    }

    /**
     * Test of setOperator method, of class OperatorPanel.
     */
    @Test
    public void testSetOperator() {
        Operator operator = Operator.Equivalence;
        OperatorPanel instance = new OperatorPanel();
        instance.setOperator(operator);
        Operator expResult = operator;
        Operator result = instance.getOperator();
        assertEquals(expResult, result);
    }
}
