/*
 *   Project: Speedith.Core
 * 
 * File name: Isabelle2010ExportProvider.java
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

import speedith.core.lang.SpiderDiagram;

import java.io.IOException;
import java.io.Writer;
import java.util.Locale;
import java.util.Map;

/**
 * A stupid test export format provider.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class TestExportProvider extends SDExportProvider {

    public static final String Description = "A dummy testing export provider.";
    public static final String ExportContent = "Blabla";
    /**
     * The name of the export format of this provider.
     */
    public static final String FormatName = "DummyExportProvider";

    @Override
    public String getFormatName() {
        return FormatName;
    }

    @Override
    public SDExporter getExporter(Map<String, String> parameters) {
        return new Exporter();
    }

    @Override
    public String getDescription(Locale locale) {
        return Description;
    }

    private static class Exporter extends SDExporter {

        @Override
        public void exportTo(SpiderDiagram spiderDiagram, Writer output) throws IOException {
            output.append(ExportContent);
        }
    }
}
