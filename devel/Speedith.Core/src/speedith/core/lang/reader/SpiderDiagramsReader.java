/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderDiagramsReader.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.SpiderDiagramsParser.spiderDiagram_return;
import static speedith.core.i18n.Translations.i18n;

/**
 * This class provides static methods for reading spider diagrams (in a textual
 * form) and from it producing corresponding Java objects (of type
 * {@link SpiderDiagram}).
 * <p>The syntax of the textual representation of spider diagrams is specified
 * in the 'SpiderDiagrams.g' ANTLR file (which generates the
 * {@link SpiderDiagramsParser parser} and the {@link SpiderDiagramsLexer
 * lexer}).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagramsReader {

    // TODO: Document the functions below.

    public static SpiderDiagram readSpiderDiagram(String input) throws ParseException {
        return readSpiderDiagram(new ANTLRStringStream(input));
    }

    public static SpiderDiagram readSpiderDiagram(Reader reader) throws ParseException, IOException {
        return readSpiderDiagram(new ANTLRReaderStream(reader));
    }

    public static SpiderDiagram readSpiderDiagram(InputStream iStream) throws ParseException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(iStream));
    }

    public static SpiderDiagram readSpiderDiagram(InputStream iStream, String encoding) throws ParseException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(iStream, encoding));
    }

    // TODO: Here for testing. Will be removed (or moved into a JUnit test) eventually.
    public static void main(String[] args) throws ParseException {
        readSpiderDiagram("BinarySD {arg1 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])], sh_zones = [}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" ");
    }

    private static SpiderDiagram readSpiderDiagram(CharStream chrStream) throws ParseException {
        SpiderDiagramsLexer lexer = new SpiderDiagramsLexer(chrStream);
        SpiderDiagramsParser parser = new SpiderDiagramsParser(new CommonTokenStream(lexer));
        try {
            spiderDiagram_return spiderDiagram = parser.spiderDiagram();
        } catch (ParseException pe) {
            System.out.println("Test..." + pe.getMessage());
        } catch (RecognitionException re) {
            throw new ParseException(i18n("ERR_PARSE_INVALID_SYNTAX"), re);
        }
        throw new RuntimeException("Not implemented.");
        // TODO: Implement.
    }
}
