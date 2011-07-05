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

import java.util.Arrays;
import java.util.LinkedList;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;
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
        Operator expResult = Operator.fromString(Operator.OP_NAME_IMP);
        Operator result = sd.getOperator();
        assertEquals(expResult, result);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2);
        Operator expResult1 = Operator.fromString(Operator.OP_NAME_NOT);
        Operator result1 = sd1.getOperator();
        assertEquals(expResult1, result1);

        CompoundSpiderDiagram sd2 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7);
        Operator expResult2 = Operator.fromString(Operator.OP_NAME_AND);
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

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return SpiderDiagrams.createNullSD();
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);
        
        assertTrue(sd1.equalsSemantically(transformedSD));
        assertTrue(!sd1.equalsSemantically(sd));
        assertTrue(!sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform2() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            private boolean done = false;

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                done = true;
                return SpiderDiagrams.createNullSD();
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return done;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{SpiderDiagrams.createNullSD(), sd.getOperand(1)})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);
        
        assertTrue(sd1.equalsSemantically(transformedSD));
        assertTrue(!sd1.equalsSemantically(sd));
        assertTrue(!sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform3() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                if (childIndex == 1) {
                    return SpiderDiagrams.createNullSD();
                } else {
                    return psd;
                }
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);
        
        assertTrue(sd1.equalsSemantically(transformedSD));
        assertTrue(!sd1.equalsSemantically(sd));
        assertTrue(!sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform4() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                if (diagramIndex == 2) {
                    return SpiderDiagrams.createNullSD();
                } else {
                    return psd;
                }
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).equals(transformedSD));
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})) == transformedSD);
        assertTrue(SpiderDiagrams.createCompoundSD(Operator.OP_NAME_IMP, Arrays.asList(new SpiderDiagram[]{sd.getOperand(0), SpiderDiagrams.createNullSD()})).hashCode() == transformedSD.hashCode());
        assertFalse(sd.equals(transformedSD));
        assertFalse(sd == transformedSD);

        CompoundSpiderDiagram sd1 = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        assertTrue(sd1.equals(transformedSD));
        assertTrue(sd1 == transformedSD);
        
        assertTrue(sd1.equalsSemantically(transformedSD));
        assertTrue(!sd1.equalsSemantically(sd));
        assertTrue(!sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform5() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return psd;
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);
        
        assertTrue(sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform6() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return null;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);
        
        assertTrue(sd.equalsSemantically(transformedSD));
    }

    /**
     * Test of transform method, of class CompoundSpiderDiagram.
     */
    @Test
    public void testTransform7() throws ReadingException {
        CompoundSpiderDiagram sd = (CompoundSpiderDiagram) SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        SpiderDiagram transformedSD = sd.transform(new Transformer() {

            public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return SpiderDiagrams.createNullSD();
            }

            public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return nsd;
            }

            public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
                return csd;
            }

            public boolean isDone() {
                return false;
            }
        });
        assertTrue(sd.equals(transformedSD));
        assertTrue(sd == transformedSD);
        
        assertTrue(sd.equalsSemantically(transformedSD));
    }
}
