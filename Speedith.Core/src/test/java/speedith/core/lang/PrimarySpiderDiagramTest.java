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

import org.junit.Test;
import speedith.core.lang.reader.ReadingException;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.io.IOException;
import java.util.Arrays;
import java.util.SortedSet;
import java.util.TreeSet;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D1;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D2;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagramTest {

    @Test(expected = IllegalArgumentException.class)
    public void addShading_should_throw_an_exception_if_adding_a_zone_that_does_not_have_the_right_contours() {
        DIAGRAM_SPEEDITH_PAPER_FIG2_D1.addShading(
                Zone.fromInContours("A", "E").withOutContours("B", "D")
        );
    }

    @Test
    public void addShading_should_return_the_same_diagram_when_the_zone_is_already_shaded() {
        PrimarySpiderDiagram resultDiagram = DIAGRAM_SPEEDITH_PAPER_FIG2_D2.addShading(
                Zone.fromInContours("A", "E", "C").withOutContours("F")
        );

        assertThat(
                resultDiagram,
                equalTo(DIAGRAM_SPEEDITH_PAPER_FIG2_D2)
        );
    }

    @Test
    public void addShading_should_return_diagram_with_new_shading() {
        Zone newShadedZone = Zone.fromInContours("A", "E").withOutContours("F", "C");
        PrimarySpiderDiagram resultDiagram = DIAGRAM_SPEEDITH_PAPER_FIG2_D2.addShading(newShadedZone);
        SortedSet<Zone> expectedShadedZones = new TreeSet<>(DIAGRAM_SPEEDITH_PAPER_FIG2_D2.getShadedZones());
        expectedShadedZones.add(newShadedZone);

        assertThat(
                resultDiagram.getShadedZones(),
                equalTo(expectedShadedZones)
        );
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
        assertEquals(new TreeSet<>(Arrays.asList("s1")), psd.getSpidersInZone(z));
        assertEquals(new TreeSet<String>(), psd.getSpidersInZone(Zone.fromOutContours("A", "B")));

        csd = (CompoundSpiderDiagram) TestSpiderDiagrams.readSpiderDiagramFromSDTFile(1);
        psd = (PrimarySpiderDiagram) csd.getOperand(0);
        assertEquals(new TreeSet<>(Arrays.asList("s1", "s2")), psd.getSpidersInZone(Zone.fromInContours("B").withOutContours("A", "C")));
        psd = (PrimarySpiderDiagram) csd.getOperand(1);
        assertEquals(new TreeSet<>(Arrays.asList("t1", "t2", "t3")), psd.getSpidersInZone(Zone.fromInContours("B")));
    }
}