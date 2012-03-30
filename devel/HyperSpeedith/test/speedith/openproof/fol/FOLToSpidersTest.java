/*
 *   Project: HyperSpeedith
 * 
 * File name: FOLToSpidersTest.java
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
package speedith.openproof.fol;

import java.util.logging.Level;
import java.util.logging.Logger;
import openproof.fol.representation.OPFormula;
import openproof.fol.representation.parser.StringToFormulaParser;
import org.junit.*;
import static org.junit.Assert.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.export.ExportException;
import speedith.core.lang.export.OpenproofExportProvider;
import speedith.core.lang.export.SDExporter;
import speedith.core.lang.export.SDExporting;
import speedith.core.lang.reader.SpiderDiagramsReader;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class FOLToSpidersTest {

	public static final String SD_EXAMPLE_1 = "BinarySD {arg1 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"t1\", [([\"A\", \"B\"], [])]), (\"t2\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"t2\", [([\"A\", \"B\"], [])]), (\"t1\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op |\" }";

	public FOLToSpidersTest() {
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
	public void testConvert() throws Exception {
		OPFormula formula = getOPFormulaFromSpider(SD_EXAMPLE_1);
		SpiderDiagram expResult = SpiderDiagramsReader.readSpiderDiagram(SD_EXAMPLE_1);
		SpiderDiagram result = FOLToSpiders.convert(formula);
		assertEquals(expResult, result);
	}

	public OPFormula getOPFormulaFromSpider(String sd) {
		try {
			SDExporter exporter = SDExporting.getProvider(OpenproofExportProvider.FormatName).getExporter(null);
			String exportedDiagram = exporter.export(SpiderDiagramsReader.readSpiderDiagram(sd));
			return StringToFormulaParser.getFormula(exportedDiagram);
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}
}
