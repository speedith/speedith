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
import java.util.SortedSet;
import java.util.TreeSet;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import speedith.core.lang.BinarySpiderDiagram;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.UnarySpiderDiagram;
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
    public static final String ARG1 = "arg1";
    public static final String ARG2 = "arg2";
    public static final String OPERATOR = "operator";

    // TODO: Document the functions below.
    public static SpiderDiagram readSpiderDiagram(String input) throws ReadingException {
        return readSpiderDiagram(new ANTLRStringStream(input));
    }

    public static SpiderDiagram readSpiderDiagram(Reader reader) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRReaderStream(reader));
    }

    public static SpiderDiagram readSpiderDiagram(InputStream iStream) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(iStream));
    }

    public static SpiderDiagram readSpiderDiagram(InputStream iStream, String encoding) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(iStream, encoding));
    }

    // TODO: Here for testing. Will be removed (or moved into a JUnit test) eventually.
    public static void main(String[] args) throws ReadingException {
        readSpiderDiagram("BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])], sh_zones = []}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }");
    }

    private static String getKeyFromPair(CommonTree childTree) {
        return childTree.getChild(0).getText();
    }

    private static SpiderDiagram readSpiderDiagram(CharStream chrStream) throws ReadingException {
        SpiderDiagramsLexer lexer = new SpiderDiagramsLexer(chrStream);
        SpiderDiagramsParser parser = new SpiderDiagramsParser(new CommonTokenStream(lexer));
        try {
            return toSpiderDiagram(parser.spiderDiagram());
        } catch (RecognitionException re) {
            throw new ReadingException(i18n("ERR_PARSE_INVALID_SYNTAX"), re);
        } catch (ParseException pe) {
            throw new ReadingException(pe.getMessage(), pe.getCause());
        }
    }

    // <editor-fold defaultstate="collapsed" desc="Translation Methods (from the AST to SpiderDiagrams)">
    private static SpiderDiagram toSpiderDiagram(spiderDiagram_return spiderDiagram) throws ReadingException {
        if (spiderDiagram == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "spiderDiagram"));
        }
        return toSpiderDiagram(spiderDiagram.tree);
    }

    private static SpiderDiagram toSpiderDiagram(CommonTree tree) throws ReadingException {
        if (tree == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
        }
        switch (tree.token.getType()) {
            case SpiderDiagramsParser.SD_BINARY:
                return toBinarySD(tree);
            case SpiderDiagramsParser.SD_UNARY:
                return toUnarySD(tree);
            case SpiderDiagramsParser.SD_PRIMARY:
                return toPrimary(tree);
            case SpiderDiagramsParser.SD_NULL:
                return NullSpiderDiagram.getInstance();
            default:
                throw new ReadingException(i18n("ERR_UNKNOWN_SD_TYPE"));
        }
    }

    private static BinarySpiderDiagram toBinarySD(CommonTree tree) throws ReadingException {
        if (tree == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
        }
        // operator, arg1 and arg2 are the expected arguments that a binary
        // spider diagram needs.
        String operator = null;
        SpiderDiagram arg1 = null;
        SpiderDiagram arg2 = null;
        // Go through all the children of the BinarySD tree node (all these
        // children should be key value PAIRs).
        for (Object child : tree.getChildren()) {
            CommonTree childTree = checkKeyValuePair(child);
            String key = getKeyFromPair(childTree);
            if (ARG1.equals(key)) {
                arg1 = toSpiderDiagram((CommonTree)childTree.getChild(1));
            } else if (ARG2.equals(key)) {
                arg2 = toSpiderDiagram((CommonTree)childTree.getChild(1));
            } else if (OPERATOR.equals(key)) {
                operator = childTree.getChild(1).getText();
            } else
                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", ARG1 + " | " + ARG2 + " | " + OPERATOR), childTree.getLine(), childTree.getCharPositionInLine());
        }
        if (operator == null || arg1 == null || arg2 == null)
            throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", ARG1 + " | " + ARG2 + " | " + OPERATOR), tree.getLine(), tree.getCharPositionInLine());
        return new BinarySpiderDiagram(operator, arg1, arg2);
    }

    private static UnarySpiderDiagram toUnarySD(CommonTree tree) throws ReadingException {
        if (tree == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
        }
        // operator, arg1 and arg2 are the expected arguments that a binary
        // spider diagram needs.
        String operator = null;
        SpiderDiagram arg1 = null;
        // Go through all the children of the BinarySD tree node (all these
        // children should be key value PAIRs).
        for (Object child : tree.getChildren()) {
            CommonTree childTree = checkKeyValuePair(child);
            String key = getKeyFromPair(childTree);
            if (ARG1.equals(key)) {
                arg1 = toSpiderDiagram((CommonTree)childTree.getChild(1));
            } else if (OPERATOR.equals(key)) {
                operator = childTree.getChild(1).getText();
            } else
                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", ARG1 + " | " + OPERATOR), childTree.getLine(), childTree.getCharPositionInLine());
        }
        if (operator == null || arg1 == null)
            throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", ARG1 + " & " + OPERATOR), tree.getLine(), tree.getCharPositionInLine());
        return new UnarySpiderDiagram(operator, arg1);
    }

    private static SpiderDiagram toPrimary(CommonTree tree) {
        return null;
    }

    /**
     * Checks if the given {@code node} is a {@link CommonTree} and is of type
     * {@link SpiderDiagramsParser#PAIR}. It returns the type-cast reference to
     * the node upon success, or throws an {@link ReadingException} otherwise.
     * @param node the node to check that it represents a key-value pair.
     * @return the node (properly type cast).
     * @throws ReadingException
     */
    private static CommonTree checkKeyValuePair(Object node) throws ReadingException {
        if (node instanceof CommonTree) {
            CommonTree treeNode = (CommonTree) node;
            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.PAIR) {
                return treeNode;
            } else {
                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), treeNode.getLine(), treeNode.getCharPositionInLine());
            }
        } else {
            return null;
        }
    }
    // </editor-fold>
}
