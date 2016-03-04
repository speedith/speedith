/*
 *   Project: Speedith.Core
 * 
 * File name: CompoundSpiderDiagramTest.java
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
package speedith.core.lang;

import org.junit.*;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;

import java.util.ArrayList;
import java.util.Arrays;

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CompoundSpiderDiagramTest {

    public CompoundSpiderDiagramTest() {
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
     * Test of getOperator method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testGetOperator() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        Operator expResult = Operator.fromString(Operator.Implication.getName());
        Operator result = sd.getOperator();
        assertEquals(expResult, result);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2);
        Operator expResult1 = Operator.fromString(Operator.Negation.getName());
        Operator result1 = sd1.getOperator();
        assertEquals(expResult1, result1);

        CompoundSpiderDiagram sd2 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7);
        Operator expResult2 = Operator.fromString(Operator.Conjunction.getName());
        Operator result2 = sd2.getOperator();
        assertEquals(expResult2, result2);
    }

    /**
     * Test of getSubDiagramCount method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testGetSubDiagramCount() throws ReadingException {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        assertEquals(3, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2);
        assertEquals(4, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_3);
        assertEquals(4, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_4);
        assertEquals(1, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_5);
        assertEquals(1, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_6);
        assertEquals(2, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7);
        assertEquals(3, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8);
        assertEquals(3, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9);
        assertEquals(3, sd.getSubDiagramCount());

        sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        assertEquals(3, sd.getSubDiagramCount());
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                return SpiderDiagrams.createNullSD();
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);

        assertTrue(sd1.isSEquivalentTo(transformedSD));
        assertTrue(!sd1.isSEquivalentTo(sd));
        assertTrue(!sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform2() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            private boolean done = false;

            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                done = true;
                return SpiderDiagrams.createNullSD();
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return done;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);

        assertTrue(sd1.isSEquivalentTo(transformedSD));
        assertTrue(!sd1.isSEquivalentTo(sd));
        assertTrue(!sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform3() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                if (childIndices.get(childIndices.size() - 1) == 1) {
                    return SpiderDiagrams.createNullSD();
                } else {
                    return psd;
                }
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);

        assertTrue(sd1.isSEquivalentTo(transformedSD));
        assertTrue(!sd1.isSEquivalentTo(sd));
        assertTrue(!sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform4() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                if (diagramIndex == 2) {
                    return SpiderDiagrams.createNullSD();
                } else {
                    return psd;
                }
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.Implication.getName(), Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);

        assertTrue(sd1.isSEquivalentTo(transformedSD));
        assertTrue(!sd1.isSEquivalentTo(sd));
        assertTrue(!sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform5() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                return psd;
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);

        assertTrue(sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform6() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                return null;
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return null;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);

        assertTrue(sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform7() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {
            @Override
            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, psd);
                return SpiderDiagrams.createNullSD();
            }

            @Override
            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, nsd);
                return nsd;
            }

            @Override
            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
                checkChildIndices(parents, childIndices, csd);
                return csd;
            }

            @Override
            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);

        assertTrue(sd.isSEquivalentTo(transformedSD));
    }

    /**
     * Test of visit method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testVisit1() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        int retVal = sd.visit(new DiagramVisitor<Integer>() {
            int count = 0;

            @Override
            public void init(SpiderDiagram root) {
            }

            @Override
            public void end() {
            }

            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                checkChildIndices(parents, childIndices, subDiagram);
                ++count;
            }

            @Override
            public boolean isDone() {
                return false;
            }

            @Override
            public Integer getResult() {
                return count;
            }
        });
        assertEquals(3, retVal);
    }

    /**
     * Test of visit method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testVisit2() throws ReadingException {
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_3));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_6));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_11));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_12));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_13));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_14));
        checkVisitSD((CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_15));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_3));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_4));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_5));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_6));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_11));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_12));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_13));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_14));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_15));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_16));
        checkSDCollection(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_17));
    }

    /**
     * Test of iterator method, of class CompoundSpiderDiagram.
     *
     * @throws ReadingException
     */
    @Test
    public void testIterator() throws ReadingException {
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_3));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_4));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_5));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_6));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_11));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_12));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_13));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_14));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_15));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_16));
        checkSDIterator(SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_17));
    }

    //<editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    private void checkVisitSD(CompoundSpiderDiagram sd) {
        for (int i = 0; i < sd.getSubDiagramCount(); i++) {
            final int targetSD = i;
            SpiderDiagram retVal = sd.visit(new DiagramVisitor<SpiderDiagram>() {
                private SpiderDiagram sd = null;

                @Override
                public void init(SpiderDiagram root) {
                }

                @Override
                public void end() {
                }

                @Override
                public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                    checkChildIndices(parents, childIndices, subDiagram);
                    if (subDiagramIndex == targetSD) {
                        sd = subDiagram;
                    }
                }

                @Override
                public boolean isDone() {
                    return sd != null;
                }

                @Override
                public SpiderDiagram getResult() {
                    return sd;
                }
            });
            assertEquals(sd.getSubDiagramAt(targetSD), retVal);
        }
    }

    private static void checkSDCollection(SpiderDiagram sd) {
        ArrayList<SpiderDiagram> retVal = sd.visit(new DiagramVisitor<ArrayList<SpiderDiagram>>() {
            private ArrayList<SpiderDiagram> collectedSDs = new ArrayList<>();

            @Override
            public void init(SpiderDiagram root) {
            }

            @Override
            public void end() {
            }

            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                checkChildIndices(parents, childIndices, subDiagram);
                assertEquals(collectedSDs.size(), subDiagramIndex);
                collectedSDs.add(subDiagram);
            }

            @Override
            public boolean isDone() {
                return false;
            }

            @Override
            public ArrayList<SpiderDiagram> getResult() {
                return collectedSDs;
            }
        }, true);
        for (int i = 0; i < sd.getSubDiagramCount(); i++) {
            assertSame(sd.getSubDiagramAt(i), retVal.get(i));
        }
    }

    private void checkSDIterator(SpiderDiagram sd) {
        int i = 0;
        for (SpiderDiagram ssd : sd) {
            assertSame(sd.getSubDiagramAt(i++), ssd);
        }
        assertEquals(i, sd.getSubDiagramCount());
    }

    private static void checkChildIndices(ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, SpiderDiagram curSD) {
        assertNotNull(parents);
        if (parents.size() > 0) {
            final int size = childIndices.size();
            assertEquals(size, parents.size());
            for (int i = 0; i < size - 1; i++) {
                Integer parentChildIndex = childIndices.get(i);
                assertSame(parents.get(i).getOperand(parentChildIndex), parents.get(i + 1));
            }
            assertSame(parents.get(size - 1).getOperand(childIndices.get(size - 1)), curSD);
        }
    }
    //</editor-fold>
}
