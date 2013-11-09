/*
 *   Project: Speedith.Core
 * 
 * File name: PrimarySpiderDiagramTest.java
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
package speedith.core.lang;

import java.io.IOException;
import java.util.Arrays;
import java.util.TreeSet;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import static org.junit.Assert.*;
import speedith.core.lang.reader.ReadingException;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagramTest {

    public PrimarySpiderDiagramTest() {
    }

    @BeforeClass
    public static void setUpClass() {
    }

    @AfterClass
    public static void tearDownClass() {
    }

    @Before
    public void setUp() {
    }

    @After
    public void tearDown() {
    }

    /**
     * Test of getAllContours method, of class PrimarySpiderDiagram.
     */
    @Test
    public void testGetAllContours() throws ReadingException, IOException {
        CompoundSpiderDiagram csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(0);
        PrimarySpiderDiagram psd = (PrimarySpiderDiagram) csd.getOperand(0);
        TreeSet<String> contoursAB = new TreeSet<>(Arrays.asList("A", "B"));
        assertEquals(contoursAB, psd.getAllContours());

        TreeSet<String> contoursABC = new TreeSet<>(Arrays.asList("A", "B", "C"));
        csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(1);
        psd = (PrimarySpiderDiagram) csd.getOperand(0);
        assertEquals(contoursABC, psd.getAllContours());

        TreeSet<String> contoursB = new TreeSet<>(Arrays.asList("B"));
        psd = (PrimarySpiderDiagram) csd.getOperand(1);
        assertEquals(contoursB, psd.getAllContours());

        TreeSet<String> contoursBD = new TreeSet<>(Arrays.asList("B", "D"));
        csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(2);
        psd = (PrimarySpiderDiagram) csd.getOperand(1);
        assertEquals(contoursBD, psd.getAllContours());
    }

    /**
     * Test of getSpiderCountInZone method, of class PrimarySpiderDiagram.
     */
    @Test
    public void testGetSpiderCountInZone() throws ReadingException, IOException {
        CompoundSpiderDiagram csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(0);
        PrimarySpiderDiagram psd = (PrimarySpiderDiagram) csd.getOperand(0);
        Zone z = Zone.fromInContours("A", "B");
        assertEquals(1, psd.getSpiderCountInZone(z));
        assertEquals(0, psd.getSpiderCountInZone(Zone.fromOutContours("A", "B")));

        csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(1);
        psd = (PrimarySpiderDiagram) csd.getOperand(0);
        assertEquals(2, psd.getSpiderCountInZone(Zone.fromInContours("B").withOutContours("A", "C")));
        psd = (PrimarySpiderDiagram) csd.getOperand(1);
        assertEquals(3, psd.getSpiderCountInZone(Zone.fromInContours("B")));
    }

    /**
     * Test of getSpidersInZone method, of class PrimarySpiderDiagram.
     */
    @Test
    public void testGetSpidersInZone() throws ReadingException, IOException {
        CompoundSpiderDiagram csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(0);
        PrimarySpiderDiagram psd = (PrimarySpiderDiagram) csd.getOperand(0);
        Zone z = Zone.fromInContours("A", "B");
        assertEquals(new TreeSet<>(Arrays.asList("s")), psd.getSpidersInZone(z));
        assertEquals(new TreeSet<String>(), psd.getSpidersInZone(Zone.fromOutContours("A", "B")));

        csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(1);
        psd = (PrimarySpiderDiagram) csd.getOperand(0);
        assertEquals(new TreeSet<>(Arrays.asList("s1", "s2")), psd.getSpidersInZone(Zone.fromInContours("B").withOutContours("A", "C")));
        psd = (PrimarySpiderDiagram) csd.getOperand(1);
        assertEquals(new TreeSet<>(Arrays.asList("t1", "t2", "t3")), psd.getSpidersInZone(Zone.fromInContours("B")));
    }
}