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

import java.io.UnsupportedEncodingException;
import openproof.fol.representation.OPFormula;
import openproof.fol.representation.parser.ParseException;
import openproof.fol.representation.parser.StringToFormulaParser;
import static org.junit.Assert.*;
import org.junit.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.export.ExportException;
import speedith.core.lang.export.OpenproofExportProvider;
import speedith.core.lang.export.SDExporter;
import speedith.core.lang.export.SDExporting;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class FOLToSpidersTest {

	public static final String SD_EXAMPLE_1 = "BinarySD {arg1 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [], habitats = [(\"t1\", [([\"A\", \"B\"], [])]), (\"t2\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [], habitats = [(\"t2\", [([\"A\", \"B\"], [])]), (\"t1\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op |\" }";
	public static final String SD_EXAMPLE_2 = "BinarySD {arg1 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [], habitats = [(\"t1\", [([\"A\", \"B\"], [])]), (\"t2\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"t1\", \"t2\"], sh_zones = [], habitats = [(\"t2\", [([\"A\", \"B\"], [])]), (\"t1\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op -->\" }";
	public static final String OP_EXAMPLE_1 = "(/t1(/t2((t1 # t2) & A(t1) & B(t1) & ((A(t2) & ~B(t2)) | (B(t2) & ~A(t2)))))) | (/t1(/t2((t1 # t2) & ((A(t1) & ~B(t1)) | (B(t1) & ~A(t1))) & A(t2) & B(t2))))";

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
		convCheckWithSDString(SD_EXAMPLE_1);
		convCheckWithSDString(SD_EXAMPLE_2);

		checkConversionToFrom(OP_EXAMPLE_1, false, SpiderDiagramsReader.readSpiderDiagram(SD_EXAMPLE_1));
	}

	private void convCheckWithSDString(String exampleSDString) throws ReadingException, ConversionException {
		OPFormula formula;
		SpiderDiagram expResult;
		SpiderDiagram result;
		formula = getOPFormulaFromSpider(exampleSDString);
		expResult = SpiderDiagramsReader.readSpiderDiagram(exampleSDString);
		result = FOLToSpiders.convert(formula);
		assertEquals(expResult, result);
	}

	public OPFormula getOPFormulaFromSpider(String sd) {
		try {
			SDExporter exporter = SDExporting.getProvider(OpenproofExportProvider.FormatName).getExporter(null);
			String exportedDiagram = exporter.export(SpiderDiagramsReader.readSpiderDiagram(sd));
			System.out.println(exportedDiagram);
			return StringToFormulaParser.getFormula(exportedDiagram);
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	public static void checkConversionToFrom(String opFormulaString, boolean shouldFail, SpiderDiagram expectedDiagram) throws ParseException, UnsupportedEncodingException, ExportException {
		OPFormula opFormula = StringToFormulaParser.getFormula(opFormulaString);
		try {
			SpiderDiagram convertedSD = FOLToSpiders.convert(opFormula);
			if (shouldFail) {
				fail("The conversion should fail.");
			}
			SDExporter exporter = SDExporting.getProvider(OpenproofExportProvider.FormatName).getExporter(null);
			String opFormula2 = exporter.export(convertedSD);
			SpiderDiagram convertedSD2 = FOLToSpiders.convert(StringToFormulaParser.getFormula(opFormula2));
			assertEquals(convertedSD, convertedSD2);
			if (expectedDiagram != null) {
				assertEquals(expectedDiagram, convertedSD);
			}
		} catch (ConversionException ex) {
			if (!shouldFail) {
				fail("The conversion should not fail.");
			}
		}
	}
}
