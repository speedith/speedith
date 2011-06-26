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

import java.io.File;
import java.io.FileInputStream;
import java.io.StringReader;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import speedith.core.lang.CompoundSpiderDiagram;
import static org.junit.Assert.*;
import speedith.core.lang.SpiderDiagram;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagramsReaderTest {

    public static final String SD_EXAMPLE_1 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_2 = "UnarySD {operator = \"op not\", arg1 = BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }}";
    public static final String SD_EXAMPLE_3 = "UnarySD {operator = \"op not\", arg1 = BinarySD {operator = \"op &&\", arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {} }}";
    public static final String SD_EXAMPLE_4 = "NullSD {}";
    public static final String SD_EXAMPLE_5 = "PrimarySD { spiders = [], sh_zones = [], habitats = []}";
    public static final String SD_EXAMPLE_6 = "UnarySD {operator = \"op not\", arg1 = NullSD {}}";
    public static final String SD_EXAMPLE_7 = "BinarySD {operator = \"op &&\", arg1 = NullSD {}, arg2 = NullSD {}}";
    public static final String SD_EXAMPLE_ERR_1 = "UnarySD {operator = \"op not\", ar1 = BinarySD {operator = \"op &&\", arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {} }}";
    public static final String SD_EXAMPLE_ERR_2 = "";
    public static final String SD_EXAMPLE_ERR_3 = "Primary {}";
    public static final String SD_EXAMPLE_ERR_4 = "NullSD {";
    public static final String SD_EXAMPLE_ERR_5 = "PrimarySD { spiders = [], sh__zones = [], habitats = []}";
    public static final String SD_EXAMPLE_ERR_6 = "UnarySD {operator = \", arg1 = NullSD }}";
    public static final String SD_EXAMPLE_ERR_7 = "BinarySD {operator = \"\", arg1 = NullSD {}, arg2 = NullSD {}";
    public static final String SD_EXAMPLE_ERR_8 = "BinarySD aq {operator = \"\", arg1 = NullSD {}, arg2 = NullSD {}";
    public static final String SD_EXAMPLE_ERR_9 = "BinarySD {operator = \"op ||\", arg1 = NullSD {}, arg2 = NullSD {}, arg3 = NullSD {} }";
    public static final String SD_EXAMPLE_ERR_10 = "BinarySD {operator = \"op ||\", arg1 = NullSD {}, arg2 = NullSD {}, dsaj = NullSD {} }";

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
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_String() throws Exception {
        SpiderDiagram sd1 = checkSDExample(SD_EXAMPLE_1);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram)sd1);
        SpiderDiagram sd2 = checkSDExample(SD_EXAMPLE_2);
        testGetSubDiagramAt_sd2((CompoundSpiderDiagram)sd2);
        SpiderDiagram sd3 = checkSDExample(SD_EXAMPLE_3);
        testGetSubDiagramAt_sd2((CompoundSpiderDiagram)sd3);
        SpiderDiagram sd4 = checkSDExample(SD_EXAMPLE_4);
        SpiderDiagram sd5 = checkSDExample(SD_EXAMPLE_5);
        SpiderDiagram sd6 = checkSDExample(SD_EXAMPLE_6);
        testGetSubDiagramAt_sd6((CompoundSpiderDiagram)sd6);
        SpiderDiagram sd7 = checkSDExample(SD_EXAMPLE_7);
        testGetSubDiagramAt_sd1((CompoundSpiderDiagram)sd7);
    }

    private SpiderDiagram checkSDExample(String example) throws ReadingException {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(example);
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);
        return sd;
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_String_Err() throws Exception {
        checkSDExample_Err(SD_EXAMPLE_ERR_1, 1, 30);
        checkSDExample_Err(SD_EXAMPLE_ERR_2, 0, -1);
        checkSDExample_Err(SD_EXAMPLE_ERR_3, 1, 0);
        checkSDExample_Err(SD_EXAMPLE_ERR_4, 1, 7);
        checkSDExample_Err(SD_EXAMPLE_ERR_5, 1, 26);
        checkSDExample_Err(SD_EXAMPLE_ERR_6, 1, 39);
        checkSDExample_Err(SD_EXAMPLE_ERR_7, 1, 58);
        checkSDExample_Err(SD_EXAMPLE_ERR_8, 1, 9);
        checkSDExample_Err(SD_EXAMPLE_ERR_9, 1, 66);
        checkSDExample_Err(SD_EXAMPLE_ERR_10, 1, 66);
    }

    private void checkSDExample_Err(String example, int errorLine, int errorCharIndex) {
        SpiderDiagram sd = null;
        try {
            sd = SpiderDiagramsReader.readSpiderDiagram(example);
            fail("An exception should have been thrown.");
        } catch (ReadingException readingException) {
//            System.out.println(readingException);
            assertEquals(errorLine, readingException.getLineNumber());
            assertEquals(errorCharIndex, readingException.getCharIndex());
        }
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
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
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_Reader2() throws Exception {
        try {
            SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new StringReader(SD_EXAMPLE_ERR_2));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 0);
            assertEquals(readingException.getCharIndex(), -1);
        }
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_InputStream() throws Exception {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new FileInputStream("./test/speedith/core/lang/reader/ParserExample1.sd"));
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_InputStream2() throws Exception {
        try {
            SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new FileInputStream("./test/speedith/core/lang/reader/ParserExample1_1.sd"));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 6);
            assertEquals(readingException.getCharIndex(), 8);
        }
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_File() throws Exception {
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new File("./test/speedith/core/lang/reader/ParserExample1.sd"));
        String str1 = sd.toString();
        SpiderDiagram sd2 = SpiderDiagramsReader.readSpiderDiagram(str1);
        assertEquals(str1, sd2.toString());
        assertEquals(sd, sd2);
        assertTrue(sd == sd2);
    }

    /**
     * Test of readSpiderDiagram method, of class SpiderDiagramsReader.
     * @throws Exception
     */
    @Test
    public void testReadSpiderDiagram_File2() throws Exception {
        try {
            SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(new File("./test/speedith/core/lang/reader/ParserExample1_1.sd"));
        } catch (ReadingException readingException) {
            assertEquals(readingException.getLineNumber(), 6);
            assertEquals(readingException.getCharIndex(), 8);
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
        assertTrue(((CompoundSpiderDiagram)csd.getOperand(0)).getOperand(1).equals(csd.getSubDiagramAt(3)));
        assertTrue(((CompoundSpiderDiagram)csd.getOperand(0)).getOperand(1) == (csd.getSubDiagramAt(3)));
        
        assertTrue(((CompoundSpiderDiagram)csd.getOperand(0)).getOperand(0).equals(csd.getSubDiagramAt(2)));
        assertTrue(((CompoundSpiderDiagram)csd.getOperand(0)).getOperand(0) == (csd.getSubDiagramAt(2)));
        
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
}
