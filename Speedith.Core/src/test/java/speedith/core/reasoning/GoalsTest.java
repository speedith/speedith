/*
 *   Project: Speedith.Core
 * 
 * File name: GoalsTest.java
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
package speedith.core.reasoning;

import org.junit.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class GoalsTest {
    
    public GoalsTest() {
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
     * Test of getGoals method, of class Goals.
     */
    @Test
    public void testGetGoals() throws ReadingException, IOException {
        SpiderDiagram sd1 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_1.sd"));
        Goals instance = Goals.createGoalsFrom(sd1);
        assertEquals(1, instance.getGoalsCount());
        assertSame(instance.getGoalAt(0), sd1);
        List<SpiderDiagram> goals = instance.getGoals();
        assertEquals(goals, Arrays.asList(sd1));
        try {
            goals.add(sd1);
            assertTrue("An exception should have been thrown.", false);
        } catch (UnsupportedOperationException e) {
            assertNotNull(e);
        }
    }

    /**
     * Test of getGoalAt method, of class Goals.
     */
    @Test
    public void testGetGoalAt() {
    }

    /**
     * Test of getGoalsCount method, of class Goals.
     */
    @Test
    public void testGetGoalsCount() {
    }

    /**
     * Test of createGoalsFrom method, of class Goals.
     */
    @Test
    public void testCreateGoalsFrom_List() throws ReadingException, IOException {
        SpiderDiagram sd1 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_1.sd"));
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_2.sd"));
        Goals instance = Goals.createGoalsFrom(Arrays.asList(sd1, sd2));
        assertEquals(2, instance.getGoalsCount());
        assertSame(instance.getGoalAt(0), sd1);
        assertSame(instance.getGoalAt(1), sd2);
        List<SpiderDiagram> goals = instance.getGoals();
        assertEquals(goals, Arrays.asList(sd1, sd2));
        try {
            goals.add(sd2);
            assertTrue("An exception should have been thrown.", false);
        } catch (UnsupportedOperationException e) {
            assertNotNull(e);
        }
    }

    /**
     * Test of createGoalsFrom method, of class Goals.
     */
    @Test
    public void testCreateGoalsFrom_SpiderDiagramArr() throws ReadingException, IOException {
        String spiderDiagramFile1 = "/speedith/core/lang/reader/SpiderDiagramExample_1.sd";
        SpiderDiagram sd1 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile(spiderDiagramFile1));
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_2.sd"));
        Goals instance = Goals.createGoalsFrom(sd1, sd2);
        assertEquals(2, instance.getGoalsCount());
        assertSame(instance.getGoalAt(0), sd1);
        assertSame(instance.getGoalAt(1), sd2);
        List<SpiderDiagram> goals = instance.getGoals();
        assertEquals(goals, Arrays.asList(sd1, sd2));
        try {
            goals.add(sd2);
            assertTrue("An exception should have been thrown.", false);
        } catch (UnsupportedOperationException e) {
            assertNotNull(e);
        }
    }

    public static InputStream getSpiderDiagramTestFile(String absolutePath) {
        InputStream spiderDiagramFileStream = GoalsTest.class.getResourceAsStream(absolutePath);
        if (spiderDiagramFileStream == null) {
            throw new RuntimeException("Could not open file: " + absolutePath);
        }
        return spiderDiagramFileStream;
    }

    /**
     * Test of createGoalsFrom method, of class Goals.
     */
    @Test
    public void testCreateGoalsFrom_ArrayList() throws ReadingException, IOException {
        SpiderDiagram sd1 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_1.sd"));
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(getSpiderDiagramTestFile("/speedith/core/lang/reader/SpiderDiagramExample_2.sd"));
        Goals instance = Goals.createGoalsFrom(new ArrayList<>(Arrays.asList(sd1, sd2)));
        assertEquals(2, instance.getGoalsCount());
        assertSame(instance.getGoalAt(0), sd1);
        assertSame(instance.getGoalAt(1), sd2);
        List<SpiderDiagram> goals = instance.getGoals();
        assertEquals(goals, Arrays.asList(sd1, sd2));
        try {
            goals.add(sd2);
            assertTrue("An exception should have been thrown.", false);
        } catch (UnsupportedOperationException e) {
            assertNotNull(e);
        }
    }
}
