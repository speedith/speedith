/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderDiagramsReaderTest.java
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
package speedith.core.lang.reader;

import org.junit.*;
import propity.util.Maps;
import speedith.core.lang.*;
import speedith.core.reasoning.GoalsTest;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.TreeSet;

import static org.junit.Assert.*;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagramsReaderTest {

    public static final String SD_EXAMPLE_1 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_2 = "UnarySD {operator = \"op not\", arg1 = BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }}";
    public static final String SD_EXAMPLE_3 = "UnarySD {operator = \"op not\", arg1 = BinarySD {operator = \"op &\", arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {} }}";
    public static final String SD_EXAMPLE_4 = "NullSD {}";
    public static final String SD_EXAMPLE_5 = "PrimarySD { spiders = [], sh_zones = [], habitats = [], present_zones=[([],[])]}";
    public static final String SD_EXAMPLE_6 = "UnarySD {operator = \"op not\", arg1 = NullSD {}}";
    public static final String SD_EXAMPLE_7 = "BinarySD {operator = \"op &\", arg1 = NullSD {}, arg2 = NullSD {}}";
    public static final String SD_EXAMPLE_8 = "BinarySD {operator = \"op -->\", arg1 = NullSD {}, arg2 = NullSD {}}";
    public static final String SD_EXAMPLE_9 = "BinarySD {arg1 = NullSD {}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_10 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_11 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_12 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op <-->\" }";
    public static final String SD_EXAMPLE_13 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op &\" }";
    public static final String SD_EXAMPLE_14 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op |\" }";
    public static final String SD_EXAMPLE_15 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])], present_zones = [([],[\"A\",\"B\"])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [\"B\"])]), (\"s'\", [([\"B\"], [\"A\"])])], sh_zones = [], present_zones = [([],[\"A\",\"B\"])]}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_16 = "PrimarySD { spiders = [\"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\"], [\"C\", \"D\", \"B\"]), ([\"A\", \"D\"], [\"C\", \"B\"])])], present_zones=[([],[\"A\",\"B\",\"C\",\"D\"])]}";
    public static final String SD_EXAMPLE_17 = "PrimarySD { spiders = [\"s1\", \"s2\"], sh_zones = [([\"A\", \"B\"], [])], habitats = [(\"s1\", [([\"A\"], [\"B\"])]), (\"s2\", [([\"B\"], [\"A\"])])], present_zones = [([\"A\", \"B\"], []),([],[\"A\", \"B\"])]}";
    public static final String SD_EXAMPLE_18 = "PrimarySD { spiders = [\"s1\", \"s2\", \"s3\", \"s4\"], sh_zones = [([\"A\", \"B\"], [])], habitats = [(\"s1\", [([\"A\"], [\"B\"])]), (\"s2\", [([\"B\"], [\"A\"])]), (\"s3\", [([\"B\"], [\"A\"])]), (\"s4\", [([\"B\"], [\"A\"])])], present_zones = [([\"A\", \"B\"], [])]}";
    public static final String SD_EXAMPLE_19 = "PrimarySD { spiders = [\"s1\", \"s2\"], sh_zones = [([\"A\", \"B\"], [])], habitats = [(\"s1\", [([\"A\"], [\"B\"]), ([\"A\", \"B\"], [])]), (\"s2\", [([\"B\"], [\"A\"])])], present_zones = [([\"A\", \"B\"], []),([], [\"A\", \"B\"])]}";
    public static final String SD_EXAMPLE_ERR_1 = "UnarySD {operator = \"op not\", ar1 = BinarySD {operator = \"op &\", arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {} }}";
    public static final String SD_EXAMPLE_ERR_2 = "";
    public static final String SD_EXAMPLE_ERR_3 = "Primary {}";
    public static final String SD_EXAMPLE_ERR_4 = "NullSD {";
    public static final String SD_EXAMPLE_ERR_5 = "PrimarySD { spiders = [], sh__zones = [], habitats = []}";
    public static final String SD_EXAMPLE_ERR_6 = "UnarySD {operator = \", arg1 = NullSD }}";
    public static final String SD_EXAMPLE_ERR_7 = "BinarySD {operator = \"\", arg1 = NullSD {}, arg2 = NullSD {}";
    public static final String SD_EXAMPLE_ERR_8 = "BinarySD aq {operator = \"\", arg1 = NullSD {}, arg2 = NullSD {}";
    public static final String SD_EXAMPLE_ERR_9 = "BinarySD {operator = \"op |\", arg1 = NullSD {}, arg2 = NullSD {}, arg3 = NullSD {} }";
    public static final String SD_EXAMPLE_ERR_10 = "BinarySD {operator = \"op |\", arg1 = NullSD {}, arg2 = NullSD {}, dsaj = NullSD {} }";
    public static final String REGION_EXAMPLE_1 = "[([\"A\"], [\"B\"]), ([\"C\"], [\"D\"])]";
    public static final String REGION_EXAMPLE_2 = "[]";
    public static final String REGION_EXAMPLE_3 = "[([], [\"B\"]), ([\"C\"], [])]";
    public static final String REGION_EXAMPLE_4 = "[([], [\"B\", \"A\"]), ([\"C\", \"D\"], [])]";

    public SpiderDiagramsReaderTest() {
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
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_String() throws Exception {
        SpiderDiagram sd1 = checkSDExample(SD_EXAMPLE_1, false);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd1);
        assertEquals(3, sd1.getSubDiagramCount());

        SpiderDiagram sd2 = checkSDExample(SD_EXAMPLE_2, false);
        testGetSubDiagramAt_sd2((CompoundSpiderDiagram) sd2);
        assertEquals(4, sd2.getSubDiagramCount());

        SpiderDiagram sd3 = checkSDExample(SD_EXAMPLE_3, false);
        testGetSubDiagramAt_sd2((CompoundSpiderDiagram) sd3);
        assertEquals(4, sd3.getSubDiagramCount());

        SpiderDiagram sd4 = checkSDExample(SD_EXAMPLE_4, true);
        assertEquals(1, sd4.getSubDiagramCount());

        SpiderDiagram sd5 = checkSDExample(SD_EXAMPLE_5, true);
        assertEquals(1, sd5.getSubDiagramCount());

        SpiderDiagram sd6 = checkSDExample(SD_EXAMPLE_6, true);
        testGetSubDiagramAt_sd6((CompoundSpiderDiagram) sd6);
        assertEquals(2, sd6.getSubDiagramCount());

        SpiderDiagram sd7 = checkSDExample(SD_EXAMPLE_7, true);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd7);
        assertEquals(3, sd7.getSubDiagramCount());

        SpiderDiagram sd = checkSDExample(SD_EXAMPLE_8, true);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd);
        assertEquals(3, sd.getSubDiagramCount());

        sd = checkSDExample(SD_EXAMPLE_9, false);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd);
        assertEquals(3, sd.getSubDiagramCount());

        sd = checkSDExample(SD_EXAMPLE_10, false);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd);
        assertEquals(3, sd.getSubDiagramCount());

        sd = checkSDExample(SD_EXAMPLE_11, false);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd);
        assertEquals(3, sd.getSubDiagramCount());

        sd = checkSDExample(SD_EXAMPLE_15, true);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram) sd);
        assertEquals(3, sd.getSubDiagramCount());

        sd = checkSDExample(SD_EXAMPLE_16, true);
        PrimarySpiderDiagram psd = (PrimarySpiderDiagram) sd;
        assertEquals(1, psd.getSpidersCount());
        assertEquals(1, psd.getHabitatsCount());
        assertEquals(1, psd.getShadedZonesCount());
        assertEquals(1, sd.getSubDiagramCount());
        assertEquals(new TreeSet<>(Arrays.asList("s'")), psd.getSpiders());
        assertEquals(new TreeSet<>(Arrays.asList(Zone.fromInContours("A", "B").withOutContours("C", "D"))), psd.getShadedZones());
        assertEquals(Maps.createTreeMap(Arrays.asList("s'"), Arrays.asList(new Region(Zone.fromInContours("A").withOutContours("B", "C", "D"), Zone.fromInContours("A", "D").withOutContours("B", "C")))), psd.getHabitats());

        sd = checkSDExample(SD_EXAMPLE_17, true);
        psd = (PrimarySpiderDiagram) sd;
        assertEquals(2, psd.getSpidersCount());
        assertEquals(2, psd.getHabitatsCount());
        assertEquals(1, psd.getShadedZonesCount());
        assertEquals(2, psd.getPresentZonesCount());
        assertEquals(1, sd.getSubDiagramCount());
        assertEquals(new TreeSet<>(Arrays.asList("s1", "s2")), psd.getSpiders());
        assertEquals(new TreeSet<>(Arrays.asList(Zone.fromInContours("A", "B"))), psd.getShadedZones());
        assertEquals(new TreeSet<>(Arrays.asList(Zone.fromInContours("A", "B"), Zone.fromOutContours("A","B"))), psd.getPresentZones());
        assertEquals(Maps.createTreeMap(Arrays.asList("s1", "s2"), Arrays.asList(new Region(Zone.fromInContours("A").withOutContours("B")), new Region(Zone.fromInContours("B").withOutContours("A")))), psd.getHabitats());
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_String_Err() throws Exception {
        checkSDExample_Err(SD_EXAMPLE_ERR_1, 1, 30);
        checkSDExample_Err(SD_EXAMPLE_ERR_2, 1, 0);
        checkSDExample_Err(SD_EXAMPLE_ERR_3, 1, 0);
        checkSDExample_Err(SD_EXAMPLE_ERR_4, 1, 7);
        checkSDExample_Err(SD_EXAMPLE_ERR_5, 1, 26);
        checkSDExample_Err(SD_EXAMPLE_ERR_6, 1, 39);
        checkSDExample_Err(SD_EXAMPLE_ERR_7, 1, 58);
        checkSDExample_Err(SD_EXAMPLE_ERR_8, 1, 9);
        checkSDExample_Err(SD_EXAMPLE_ERR_9, 1, 65);
        checkSDExample_Err(SD_EXAMPLE_ERR_10, 1, 65);
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_Reader() throws Exception {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new StringReader(SD_EXAMPLE_2));
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);

        assertTrue(sd.isSEquivalentTo(sd2));
        assertTrue(sd2.isSEquivalentTo(sd));
        assertTrue(sd.isSEquivalentTo(sd));
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_Reader2() throws Exception {
        try {
            SpiderDiagramsReader.readSpiderDiagram(new StringReader(SD_EXAMPLE_ERR_2));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 1);
            assertEquals(readingException.getCharIndex(), 0);
        }
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_InputStream() throws Exception {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(GoalsTest.getSpiderDiagramTestFile("/speedith/core/lang/reader/ParserExample1.sd"));
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);

        assertTrue(sd.isSEquivalentTo(sd2));
        assertTrue(sd2.isSEquivalentTo(sd));
        assertTrue(sd.isSEquivalentTo(sd));
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_InputStream2() throws Exception {
        try {
            SpiderDiagramsReader.readSpiderDiagram(GoalsTest.getSpiderDiagramTestFile("/speedith/core/lang/reader/ParserExample1_1.sd"));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 6);
            assertEquals(readingException.getCharIndex(), 8);
        }
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_File() throws Exception {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(GoalsTest.getSpiderDiagramTestFile("/speedith/core/lang/reader/ParserExample1.sd"));
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);

        assertTrue(sd.isSEquivalentTo(sd2));
        assertTrue(sd2.isSEquivalentTo(sd));
        assertTrue(sd.isSEquivalentTo(sd));
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     *
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_File2() throws Exception {
        try {
            SpiderDiagramsReader.readSpiderDiagram(GoalsTest.getSpiderDiagramTestFile("/speedith/core/lang/reader/ParserExample1_1.sd"));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 6);
            assertEquals(readingException.getCharIndex(), 8);
        }
    }

    @Test
    public void testReadRegion_1() throws ReadingException {
        Region r = checkRegionExample(REGION_EXAMPLE_1);
        Region expected = new Region(Zone.fromInContours("A").withOutContours("B"), Zone.fromInContours("C").withOutContours("D"));
        assertEquals(expected, r);
        expected = new Region(Zone.fromInContours("A"), Zone.fromInContours("C").withOutContours("D"));
        assertFalse(expected.equals(r));
    }

    @Test
    public void testReadRegion_2() throws ReadingException {
        Region r = checkRegionExample(REGION_EXAMPLE_2);
        Region expected = new Region();
        assertEquals(expected, r);
        expected = new Region(new TreeSet<Zone>());
        assertEquals(expected, r);
        expected = new Region(Arrays.asList(new Zone[]{}));
        assertEquals(expected, r);
        expected = new Region((Collection<Zone>) null);
        assertEquals(expected, r);
        expected = new Region(Zone.fromInContours("A"), Zone.fromInContours("C").withOutContours("D"));
        assertFalse(expected.equals(r));
    }

    @Test
    public void testReadRegion_3() throws ReadingException {
        Region r = checkRegionExample(REGION_EXAMPLE_3);
        Region expected = new Region(Zone.fromOutContours("B"), Zone.fromInContours("C"));
        assertEquals(expected, r);
        expected = new Region(Zone.fromInContours("A"), Zone.fromInContours("C").withOutContours("D"));
        assertFalse(expected.equals(r));
    }

    @Test
    public void testReadRegion_4() throws ReadingException {
        Region r = checkRegionExample(REGION_EXAMPLE_4);
        Region expected = new Region(Zone.fromOutContours("A", "B"), Zone.fromInContours("D", "C"));
        assertEquals(expected, r);
        expected = new Region(Zone.fromInContours("A"), Zone.fromInContours("C").withOutContours("D"));
        assertFalse(expected.equals(r));
    }

    @Test
    public void testFileReading() throws ReadingException, IOException {
        for (int i = 0; i < TestSpiderDiagrams.getSpiderDiagramSDTFilesCount(); i++) {
            TestSpiderDiagrams.readSpiderDiagramFromSDTFile(i);
        }
    }

    private SpiderDiagram checkSDExample(String example, boolean isValid) throws ReadingException {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(example);
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertEquals(sd2, sd);
        assertTrue(sd.equals(sd2));
        assertTrue(sd2.equals(sd));
        assertTrue(sd == sd2);
        assertTrue(sd.isSEquivalentTo(sd2));
        assertTrue(sd2.isSEquivalentTo(sd));
        assertTrue(sd.isSEquivalentTo(sd));
        assertEquals(isValid, sd.isValid());
        return sd;
    }

    private void checkSDExample_Err(String example, int errorLine, int errorCharIndex) {
        try {
            SpiderDiagramsReader.readSpiderDiagram(example);
            fail("An exception should have been thrown.");
        } catch (ReadingException readingException) {
            assertEquals(errorLine, readingException.getLineNumber());
            assertEquals(errorCharIndex, readingException.getCharIndex());
        }
    }

    private void testGetSubDiagramAt_sd1(CompoundSpiderDiagram csd) {
        assertTrue(csd.getOperands().get(1).equals(csd.getSubDiagramAt(2)));
        assertTrue(csd.getOperands().get(1) == csd.getSubDiagramAt(2));
        assertTrue(csd.getOperands().get(0).equals(csd.getSubDiagramAt(1)));
        assertTrue(csd.getOperands().get(0) == csd.getSubDiagramAt(1));
        assertTrue(csd.equals(csd.getSubDiagramAt(0)));
        assertTrue(csd == csd.getSubDiagramAt(0));
        assertTrue(null == csd.getSubDiagramAt(3));
    }

    private void testGetSubDiagramAt_sd2(CompoundSpiderDiagram csd) {
        assertTrue(((CompoundSpiderDiagram) csd.getOperand(0)).getOperand(1).equals(csd.getSubDiagramAt(3)));
        assertTrue(((CompoundSpiderDiagram) csd.getOperand(0)).getOperand(1) == (csd.getSubDiagramAt(3)));

        assertTrue(((CompoundSpiderDiagram) csd.getOperand(0)).getOperand(0).equals(csd.getSubDiagramAt(2)));
        assertTrue(((CompoundSpiderDiagram) csd.getOperand(0)).getOperand(0) == (csd.getSubDiagramAt(2)));

        assertTrue(csd.getOperand(0).equals(csd.getSubDiagramAt(1)));
        assertTrue(csd.getOperand(0) == csd.getSubDiagramAt(1));

        assertTrue(csd.equals(csd.getSubDiagramAt(0)));
        assertTrue(csd == csd.getSubDiagramAt(0));

        assertTrue(null == csd.getSubDiagramAt(4));
    }

    private void testGetSubDiagramAt_sd6(CompoundSpiderDiagram csd) {
        assertTrue(csd.getOperand(0).equals(csd.getSubDiagramAt(1)));
        assertTrue(csd.getOperand(0) == csd.getSubDiagramAt(1));

        assertTrue(csd.equals(csd.getSubDiagramAt(0)));
        assertTrue(csd == csd.getSubDiagramAt(0));

        assertTrue(null == csd.getSubDiagramAt(2));
    }

    private Region checkRegionExample(String example) throws ReadingException {
        return SpiderDiagramsReader.readRegion(example);
    }
}
