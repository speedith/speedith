/*
 *   Project: Speedith.Core
 * 
 * File name: OpenproofExportProviderTest.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
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

import org.junit.*;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class OpenproofExportProviderTest {
    
    public OpenproofExportProviderTest() {
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
    public void testExport() throws ExportException, ReadingException {
        SDExportProvider provider = SDExporting.getProvider(OpenproofExportProvider.FormatName);
        assertEquals(OpenproofExportProvider.FormatName, provider.getFormatName());
        assertSame(provider, SDExporting.getProvider(OpenproofExportProvider.FormatName));
        SDExporter exporter = provider.getExporter(null);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_15);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_14);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_13);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_12);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_11);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_10);
        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_18);
//        exportDiagram(exporter, SpiderDiagramsReaderTest.SD_EXAMPLE_3);
    }

    private void exportDiagram(SDExporter exporter, final String sd) throws ExportException, ReadingException {
        String exportedDiagram = exporter.export(SpiderDiagramsReader.readSpiderDiagram(sd));
//        System.out.println(exportedDiagram);
    }
}
