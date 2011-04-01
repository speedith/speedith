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

import java.util.AbstractMap.SimpleEntry;
import speedith.core.lang.Region;
import java.util.Map;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import speedith.core.lang.BinarySpiderDiagram;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.UnarySpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.reader.SpiderDiagramsParser.spiderDiagram_return;
import sun.security.jca.GetInstance.Instance;
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
    public static final String HABITATS = "habitats";
    public static final String SH_ZONES = "sh_zones";
    public static final String SPIDERS = "spiders";

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
        readSpiderDiagram("BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }");
    }

//    /**
//     * Takes the tree node that is supposed to be the STRING language element,
//     * checks that it is and tries to extract the Java string out of it.
//     * <p>Upon failure it throws an exception.</p>
//     * @param node
//     * @return
//     * @throws ReadingException
//     */
//    private static String stringFromStringNodeChecked(Object node) throws ReadingException {
//        if (node instanceof CommonTree) {
//            CommonTree treeNode = (CommonTree) node;
//            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.STRING) {
//                String str = treeNode.token.getText();
//                if (str != null && str.length() >= 2) {
//                    return str.substring(1, str.length() - 1);
//                }
//            }
//        }
//        if (node instanceof Tree) {
//            throw new ReadingException(i18n("ERR_TRANSLATE_INVALID_STRING"), ((Tree) node).getLine(), ((Tree) node).getCharPositionInLine());
//        } else {
//            throw new IllegalStateException(i18n("GERR_ILLEGAL_STATE"));
//        }
//    }
//    private static String getKeyFromPair(CommonTree childTree) {
//        return childTree.getChild(0).getText();
//    }
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
        return SDTranslator.Instance.fromASTNode(spiderDiagram.tree);
    }

//    private static SpiderDiagram toSpiderDiagram(CommonTree tree) throws ReadingException {
//        return
//        if (tree == null) {
//            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
//        }
//        switch (tree.token.getType()) {
//            case SpiderDiagramsParser.SD_BINARY:
//                return toBinarySD(tree);
//            case SpiderDiagramsParser.SD_UNARY:
//                return toUnarySD(tree);
//            case SpiderDiagramsParser.SD_PRIMARY:
//                return toPrimary(tree);
//            case SpiderDiagramsParser.SD_NULL:
//                return NullSpiderDiagram.getInstance();
//            default:
//                throw new ReadingException(i18n("ERR_UNKNOWN_SD_TYPE"));
//        }
//    }
//
//    private static BinarySpiderDiagram toBinarySD(CommonTree tree) throws ReadingException {
//        if (tree == null) {
//            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
//        }
//        // operator, arg1 and arg2 are the expected arguments that a binary
//        // spider diagram needs.
//        String operator = null;
//        SpiderDiagram arg1 = null;
//        SpiderDiagram arg2 = null;
//        // Go through all the children of the BinarySD tree node (all these
//        // children should be key value PAIRs).
//        for (Object child : tree.getChildren()) {
//            CommonTree childTree = checkKeyValuePair(child);
//            String key = getKeyFromPair(childTree);
//            if (ARG1.equals(key)) {
//                // NOTE: we allow ourselves an unchecked to CommonTree because
//                // we trust the parser to have created CommonTree instead of
//                // anything else.
//                arg1 = toSpiderDiagram((CommonTree) childTree.getChild(1));
//            } else if (ARG2.equals(key)) {
//                // NOTE: we allow ourselves an unchecked to CommonTree because
//                // we trust the parser to have created CommonTree instead of
//                // anything else.
//                arg2 = toSpiderDiagram((CommonTree) childTree.getChild(1));
//            } else if (OPERATOR.equals(key)) {
//                operator = stringFromStringNodeChecked(childTree.getChild(1));
//            } else {
//                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", ARG1 + " | " + ARG2 + " | " + OPERATOR), childTree.getLine(), childTree.getCharPositionInLine());
//            }
//        }
//        if (operator == null || arg1 == null || arg2 == null) {
//            throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", ARG1 + " | " + ARG2 + " | " + OPERATOR), tree.getLine(), tree.getCharPositionInLine());
//        }
//        return new BinarySpiderDiagram(operator, arg1, arg2);
//    }
//
//    private static UnarySpiderDiagram toUnarySD(CommonTree tree) throws ReadingException {
//        if (tree == null) {
//            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
//        }
//        // operator, arg1 and arg2 are the expected arguments that a binary
//        // spider diagram needs.
//        String operator = null;
//        SpiderDiagram arg1 = null;
//        // Go through all the children of the UnarySD tree node (all these
//        // children should be key value PAIRs).
//        for (Object child : tree.getChildren()) {
//            CommonTree childTree = checkKeyValuePair(child);
//            String key = getKeyFromPair(childTree);
//            if (ARG1.equals(key)) {
//                // NOTE: we allow ourselves an unchecked to CommonTree because
//                // we trust the parser to have created CommonTree instead of
//                // anything else.
//                arg1 = toSpiderDiagram((CommonTree) childTree.getChild(1));
//            } else if (OPERATOR.equals(key)) {
//                operator = stringFromStringNodeChecked(childTree.getChild(1));
//            } else {
//                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", ARG1 + " | " + OPERATOR), childTree.getLine(), childTree.getCharPositionInLine());
//            }
//        }
//        if (operator == null || arg1 == null) {
//            throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", ARG1 + " & " + OPERATOR), tree.getLine(), tree.getCharPositionInLine());
//        }
//        return new UnarySpiderDiagram(operator, arg1);
//    }
//
//    private static PrimarySpiderDiagram toPrimary(CommonTree tree) throws ReadingException {
//        if (tree == null) {
//            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "tree"));
//        }
//        // spiders, habitats and zones are the expected arguments to the primary
//        // spider diagram.
//        Collection<String> spiders = null;
//        Map<String, Region> habitats = null;
//        Collection<Zone> zones = null;
//        // Go through all the children of the PrimarySD tree node (all these
//        // children should be key value PAIRs).
//        for (Object child : tree.getChildren()) {
//            CommonTree childTree = checkKeyValuePair(child);
//            String key = getKeyFromPair(childTree);
//            if ("spiders".equals(key)) {
//                spiders = toList(childTree.getChild(1), StringTranslator.Instance);
//            } else if ("habitats".equals(key)) {
//                System.out.println("habitats");
//            } else if ("sh_zones".equals(key)) {
//                System.out.println("shaded zones");
//            } else {
//                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", ARG1 + " | " + OPERATOR), childTree.getLine(), childTree.getCharPositionInLine());
//            }
//        }
//        return new PrimarySpiderDiagram(spiders, habitats, zones);
//    }
    /**
     * Checks if the given {@code node} is a {@link CommonTree} and is of type
     * {@link SpiderDiagramsParser#PAIR}. It returns the type-cast reference to
     * the node upon success, or throws an {@link ReadingException} otherwise.
     * @param node the node to check that it represents a key-value pair.
     * @return the node (properly type cast).
     * @throws ReadingException
     */
//    private static CommonTree checkKeyValuePair(Object node) throws ReadingException {
//        if (node instanceof CommonTree) {
//            CommonTree treeNode = (CommonTree) node;
//            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.PAIR && treeNode.getChildCount() == 2) {
//                return treeNode;
//            }
//        }
//        if (node instanceof Tree) {
//            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), ((Tree) node).getLine(), ((Tree) node).getCharPositionInLine());
//        } else {
//            throw new IllegalStateException(i18n("GERR_ILLEGAL_STATE"));
//        }
//    }
//    private static <T> Collection<T> toList(Tree node, ElementTranslator<T> translator) throws ReadingException {
//        if (node instanceof CommonTree) {
//            CommonTree treeNode = (CommonTree) node;
//            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.LIST) {
//                if (treeNode.getChildCount() < 1) {
//                    return null;
//                }
//                ArrayList<T> objs = new ArrayList<T>(treeNode.getChildCount());
//                for (Object obj : treeNode.getChildren()) {
//                    if (obj instanceof CommonTree) {
//                        objs.add(translator.fromASTNode((CommonTree) obj));
//                    }
//                }
//                return objs;
//            }
//        }
//        if (node == null) {
//            throw new IllegalStateException(i18n("GERR_ILLEGAL_STATE"));
//        } else {
//            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), node.getLine(), node.getCharPositionInLine());
//        }
//    }
    private abstract static class ElementTranslator<T> {

        public abstract T fromASTNode(CommonTree treeNode) throws ReadingException;
    }

    private static class ZoneTranslator extends ElementTranslator<Zone> {

        public static final ZoneTranslator Instance = new ZoneTranslator();
        public static final ListTranslator<Zone> ZoneListTranslator = new ListTranslator<Zone>(Instance);
        private ListTranslator<ArrayList<String>> translator;

        private ZoneTranslator() {
            translator = new ListTranslator<ArrayList<String>>(SpiderDiagramsParser.SLIST, ListTranslator.StringListTranslator);
        }

        @Override
        public Zone fromASTNode(CommonTree treeNode) throws ReadingException {
            ArrayList<ArrayList<String>> inOutContours = translator.fromASTNode(treeNode);
            if (inOutContours == null || inOutContours.size() != 2) {
                throw new ReadingException(i18n("ERR_TRANSLATE_ZONE"), treeNode.getLine(), treeNode.getCharPositionInLine());
            }
            return new Zone(inOutContours.get(0), inOutContours.get(1));
        }
    }

    private static class HabitatTranslator extends ElementTranslator<Map<String, Region>> {

        public static final HabitatTranslator Instance = new HabitatTranslator();

        private ListTranslator<ArrayList<Object>> regionListTranslator;

        private HabitatTranslator() {
            regionListTranslator = new ListTranslator<ArrayList<Object>>(new TupleTranslator<Object>(new ElementTranslator[]{StringTranslator.Instance, ZoneTranslator.ZoneListTranslator}));
        }

        @Override
        public Map<String, Region> fromASTNode(CommonTree treeNode) throws ReadingException {
            ArrayList<ArrayList<Object>> rawHabitats = regionListTranslator.fromASTNode(treeNode);
            if (rawHabitats == null || rawHabitats.size() < 1) {
                return null;
            }
            HashMap<String, Region> habitats = new HashMap<String, Region>();
            for (ArrayList<Object> rawHabitat : rawHabitats) {
                if (rawHabitat.size() == 2) {
                    habitats.put((String)rawHabitat.get(0), new Region((ArrayList<Zone>)rawHabitat.get(1)));
                }
            }
            return habitats;
        }
    }

    private static class StringTranslator extends ElementTranslator<String> {

        public static final StringTranslator Instance = new StringTranslator();

        @Override
        public String fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.STRING) {
                String str = treeNode.token.getText();
                if (str != null && str.length() >= 2) {
                    return str.substring(1, str.length() - 1);
                }
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_INVALID_STRING"), treeNode.getLine(), treeNode.getCharPositionInLine());
        }
    }

    private static class IDTranslator extends ElementTranslator<String> {

        public static final IDTranslator Instance = new IDTranslator();

        @Override
        public String fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.ID) {
                return treeNode.token.getText();
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_INVALID_ID"), treeNode.getLine(), treeNode.getCharPositionInLine());
        }
    }

    private static abstract class GeneralSDTranslator<V extends SpiderDiagram> extends ElementTranslator<V> {

        private GeneralMapTranslator<Object> keyValueMapTranslator;

        public GeneralSDTranslator() {
        }

        private GeneralSDTranslator(int headTokenType) {
            keyValueMapTranslator = new GeneralMapTranslator<Object>(headTokenType, new HashMap<String, ElementTranslator<? extends Object>>(), null);
        }

        <T> void addMandatoryAttribute(String key, ElementTranslator<T> valueTranslator) {
            keyValueMapTranslator.typedValueTranslators.put(key, valueTranslator);
        }

        private boolean areMandatoryPresent(Map<String, Object> attributes) {
            for (String string : keyValueMapTranslator.typedValueTranslators.keySet()) {
                if (!attributes.containsKey(string)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public V fromASTNode(CommonTree treeNode) throws ReadingException {
            Map<String, Object> attrs = keyValueMapTranslator.fromASTNode(treeNode);
            if (areMandatoryPresent(attrs)) {
                return createSD(attrs);
            } else {
                throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", keyValueMapTranslator.typedValueTranslators.keySet()), treeNode.getLine(), treeNode.getCharPositionInLine());
            }
        }

        abstract V createSD(Map<String, Object> attributes);
    }

    private static class SDTranslator extends ElementTranslator<SpiderDiagram> {

        public static final SDTranslator Instance = new SDTranslator();

        private SDTranslator() {
        }

        @Override
        public SpiderDiagram fromASTNode(CommonTree treeNode) throws ReadingException {
            switch (treeNode.token.getType()) {
                case SpiderDiagramsParser.SD_BINARY:
                    return BinarySDTranslator.Instance.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_UNARY:
                    return UnarySDTranslator.Instance.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_PRIMARY:
                    return PrimarySDTranslator.Instance.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_NULL:
                    return NullSDTranslator.Instance.fromASTNode(treeNode);
                default:
                    throw new ReadingException(i18n("ERR_UNKNOWN_SD_TYPE"));
            }
        }
    }

    private static class BinarySDTranslator extends GeneralSDTranslator<BinarySpiderDiagram> {

        public static final BinarySDTranslator Instance = new BinarySDTranslator();

        private BinarySDTranslator() {
            super(SpiderDiagramsParser.SD_BINARY);
            addMandatoryAttribute(ARG1, SDTranslator.Instance);
            addMandatoryAttribute(ARG2, SDTranslator.Instance);
            addMandatoryAttribute(OPERATOR, StringTranslator.Instance);
        }

        @Override
        BinarySpiderDiagram createSD(Map<String, Object> attributes) {
            return new BinarySpiderDiagram((String) attributes.get(OPERATOR), (SpiderDiagram) attributes.get(ARG1), (SpiderDiagram) attributes.get(ARG2));
        }
    }

    private static class UnarySDTranslator extends GeneralSDTranslator<UnarySpiderDiagram> {

        public static final UnarySDTranslator Instance = new UnarySDTranslator();

        private UnarySDTranslator() {
            super(SpiderDiagramsParser.SD_UNARY);
            addMandatoryAttribute(ARG1, SDTranslator.Instance);
            addMandatoryAttribute(OPERATOR, StringTranslator.Instance);
        }

        @Override
        UnarySpiderDiagram createSD(Map<String, Object> attributes) {
            return new UnarySpiderDiagram((String) attributes.get(OPERATOR), (SpiderDiagram) attributes.get(ARG1));
        }
    }

    private static class PrimarySDTranslator extends GeneralSDTranslator<PrimarySpiderDiagram> {

        public static final PrimarySDTranslator Instance = new PrimarySDTranslator();

        private PrimarySDTranslator() {
            super(SpiderDiagramsParser.SD_PRIMARY);
            addMandatoryAttribute(SPIDERS, ListTranslator.StringListTranslator);
            addMandatoryAttribute(HABITATS, HabitatTranslator.Instance);
            addMandatoryAttribute(SH_ZONES, new ListTranslator<Zone>(ZoneTranslator.Instance));
        }

        @Override
        @SuppressWarnings("unchecked")
        PrimarySpiderDiagram createSD(Map<String, Object> attributes) {
            return new PrimarySpiderDiagram((Collection<String>) attributes.get(SPIDERS), (Map<String, Region>) attributes.get(HABITATS), (Collection<Zone>) attributes.get(SH_ZONES));
        }
    }

    private static class NullSDTranslator extends GeneralSDTranslator<NullSpiderDiagram> {

        public static final NullSDTranslator Instance = new NullSDTranslator();

        private NullSDTranslator() {
            super(SpiderDiagramsParser.SD_NULL);
        }

        @Override
        NullSpiderDiagram createSD(Map<String, Object> attributes) {
            return NullSpiderDiagram.getInstance();
        }
    }

    private static abstract class CollectionTranslator<V> extends ElementTranslator<ArrayList<V>> {

        private int headTokenType;

        public CollectionTranslator(int headTokenType) {
            if (headTokenType == SpiderDiagramsParser.SLIST || headTokenType == SpiderDiagramsParser.LIST) {
                this.headTokenType = headTokenType;
            } else {
                throw new IllegalArgumentException(i18n("GERR_ILLEGAL_ARGUMENT", "headTokenType"));
            }
        }

        @Override
        public ArrayList<V> fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == headTokenType) {
                if (treeNode.getChildCount() < 1) {
                    return null;
                }
                ArrayList<V> objs = new ArrayList<V>(treeNode.getChildCount());
                int i = 0;
                for (Object obj : treeNode.getChildren()) {
                    objs.add(fromASTChildAt(i++, (CommonTree) obj));
                }
                return objs;
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n(i18n("ERR_TRANSLATE_LIST_OR_SLIST"))), treeNode.getLine(), treeNode.getCharPositionInLine());
        }

        protected abstract V fromASTChildAt(int i, CommonTree treeNode) throws ReadingException;
    }

    private static class ListTranslator<V> extends CollectionTranslator<V> {

        public static final ListTranslator<String> StringListTranslator = new ListTranslator<String>(StringTranslator.Instance);
        ElementTranslator<? extends V> valueTranslator = null;

        public ListTranslator(ElementTranslator<? extends V> valueTranslator) {
            this(SpiderDiagramsParser.LIST, valueTranslator);
        }

        public ListTranslator(int headTokenType, ElementTranslator<? extends V> valueTranslator) {
            super(headTokenType);
            if (valueTranslator == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "valueTranslator"));
            }
            this.valueTranslator = valueTranslator;
        }

        @Override
        protected V fromASTChildAt(int i, CommonTree treeNode) throws ReadingException {
            return valueTranslator.fromASTNode(treeNode);
        }
    }

    private static class TupleTranslator<V> extends CollectionTranslator<V> {

        List<ElementTranslator<? extends V>> valueTranslators = null;

        public TupleTranslator(List<ElementTranslator<? extends V>> valueTranslators) {
            this(SpiderDiagramsParser.SLIST, valueTranslators);
        }

        public TupleTranslator(ElementTranslator<? extends V>[] valueTranslators) {
            this(SpiderDiagramsParser.SLIST, Arrays.asList(valueTranslators));
        }

        public TupleTranslator(int headTokenType, ElementTranslator<? extends V>[] valueTranslators) {
            this(headTokenType, Arrays.asList(valueTranslators));
        }

        public TupleTranslator(int headTokenType, List<ElementTranslator<? extends V>> valueTranslators) {
            super(headTokenType);
            if (valueTranslators == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "valueTranslators"));
            }
            this.valueTranslators = valueTranslators;
        }

        @Override
        protected V fromASTChildAt(int i, CommonTree treeNode) throws ReadingException {
            if (i >= valueTranslators.size()) {
                throw new ReadingException(i18n("ERR_TRANSLATE_TOO_MANY_ELMNTS"), treeNode.getLine(), treeNode.getCharPositionInLine());
            }
            return valueTranslators.get(i).fromASTNode(treeNode);
        }
    }

    private static class KeyValueTranslator<V> extends ElementTranslator<SimpleEntry<String, V>> {

        ElementTranslator<V> valueTranslator = null;

        public KeyValueTranslator(ElementTranslator<V> valueTranslator) {
            this.valueTranslator = valueTranslator;
        }

        /**
         * Checks if the given {@code node} is a {@link CommonTree} and is of type
         * {@link SpiderDiagramsParser#PAIR}. It returns the translated key-
         * value upon success, or throws an {@link ReadingException} otherwise.
         * @param treeNode the node to translate into a key-value pair.
         * @return the translated key value pair.
         * @throws ReadingException
         */
        @Override
        public SimpleEntry<String, V> fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.PAIR && treeNode.getChildCount() == 2) {
                String key = (String) IDTranslator.Instance.fromASTNode((CommonTree) treeNode.getChild(0));
                V value = valueTranslator.fromASTNode((CommonTree) treeNode.getChild(1));
                return new SimpleEntry<String, V>(key, value);
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), treeNode.getLine(), treeNode.getCharPositionInLine());
        }
    }

    private static class GeneralMapTranslator<V> extends ElementTranslator<Map<String, V>> {

        private Map<String, ElementTranslator<? extends V>> typedValueTranslators;
        private ElementTranslator<? extends V> defaultValueTranslator;
        private int headTokenType = SpiderDiagramsParser.DICT;

        public GeneralMapTranslator(Map<String, ElementTranslator<? extends V>> typedValueTranslators) {
            this(typedValueTranslators, null);
        }

        public GeneralMapTranslator(ElementTranslator<? extends V> defaultValueTranslator) {
            this(null, defaultValueTranslator);
        }

        public GeneralMapTranslator(Map<String, ElementTranslator<? extends V>> typedValueTranslators, ElementTranslator<? extends V> defaultValueTranslator) {
            this(SpiderDiagramsParser.DICT, typedValueTranslators, defaultValueTranslator);
        }

        public GeneralMapTranslator(int headTokenType, Map<String, ElementTranslator<? extends V>> typedValueTranslators, ElementTranslator<? extends V> defaultElements) {
            if (typedValueTranslators == null && defaultElements == null) {
                throw new IllegalArgumentException(i18n("ERR_ARGUMENT_ALL_NULL"));
            }
            this.typedValueTranslators = typedValueTranslators;
            this.defaultValueTranslator = defaultElements;
            this.headTokenType = headTokenType;
        }

        @Override
        public Map<String, V> fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == headTokenType) {
                if (treeNode.getChildCount() < 1) {
                    return null;
                }
                HashMap<String, V> kVals = new HashMap<String, V>();
                for (Object obj : treeNode.getChildren()) {
                    CommonTree node = (CommonTree) obj;
                    if (node.token != null && node.token.getType() == SpiderDiagramsParser.PAIR && node.getChildCount() == 2) {
                        String key = (String) IDTranslator.Instance.fromASTNode((CommonTree) node.getChild(0));
                        ElementTranslator<? extends V> translator = null;
                        if (typedValueTranslators != null) {
                            translator = typedValueTranslators.get(key);
                        } else if (defaultValueTranslator != null) {
                            translator = defaultValueTranslator;
                        }
                        if (translator == null) {
                            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_KEY_VALUE", key, typedValueTranslators == null ? "" : typedValueTranslators.keySet()), node.getLine(), node.getCharPositionInLine());
                        }
                        V value = translator.fromASTNode((CommonTree) node.getChild(1));
                        kVals.put(key, value);
                    } else {
                        throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), node.getLine(), node.getCharPositionInLine());
                    }
                }
                return kVals;
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n(i18n("ERR_TRANSLATE_LIST_OR_SLIST"))), treeNode.getLine(), treeNode.getCharPositionInLine());
        }
    }
    // </editor-fold>
}
