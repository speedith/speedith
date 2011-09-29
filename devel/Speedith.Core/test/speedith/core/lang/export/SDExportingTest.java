/*
 *   Project: Speedith.Core
 * 
 * File name: SDExportingTest.java
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

package speedith.core.lang.export;

import java.util.Set;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;
import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SDExportingTest {

    public SDExportingTest() {
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
     * Test of getExporter method, of class SDExporting.
     * @throws ReadingException 
     */
    @Test
    public void testGetExporter_String() throws ReadingException, ExportException {
        SDExporter exporter = SDExporting.getExporter(Isabelle2011ExportProvider.FormatName);
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1);
        String sdStr = exporter.export(sd);
        System.out.println(sdStr);
    }

    /**
     * Test of getSupportedFormats method, of class SDExporting.
     */
    @Test
    public void testGetSupportedFormats() {
        Set<String> supportedFormats = SDExporting.getSupportedFormats();
        assertNotNull(supportedFormats);
        assertFalse(supportedFormats.isEmpty());
        supportedFormats.contains(Isabelle2011ExportProvider.FormatName);
    }

    /**
     * Test of scanForExporters method, of class SDExporting.
     */
    @Test
    public void testScanForExporters() throws ExportException {
        // First test that the 'TestExportProvider' is not in the list of supported formats.
        Set<String> supportedFormats = SDExporting.getSupportedFormats();
        assertNotNull(supportedFormats);
        assertFalse(supportedFormats.contains(TestExportProvider.FormatName));
        
        // Now load the exporters specified in the MANIFEST...
        SDExporting.scanForExporters();
        supportedFormats = SDExporting.getSupportedFormats();
        assertNotNull(supportedFormats);
        assertTrue(supportedFormats.contains(TestExportProvider.FormatName));
        
        // And finally try to export something with it...
        SDExporter exporter = SDExporting.getExporter(TestExportProvider.FormatName);
        assertEquals(exporter.export(null), TestExportProvider.ExportContent);
        SDExportProvider provider = SDExporting.getProvider(TestExportProvider.FormatName);
        assertEquals(provider.getDescription(), TestExportProvider.Description);
    }

}