/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderDiagramsReader.java
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

import org.antlr.runtime.*;
import org.antlr.runtime.tree.CommonTree;
import speedith.core.lang.*;
import speedith.core.lang.reader.SpiderDiagramsParser.list_return;
import speedith.core.lang.reader.SpiderDiagramsParser.spiderDiagram_return;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import java.util.AbstractMap.SimpleEntry;
import java.util.*;
import java.util.Map.Entry;

import static speedith.core.i18n.Translations.i18n;
import static speedith.core.lang.CompoundSpiderDiagram.SDTextOperatorAttribute;
import static speedith.core.lang.PrimarySpiderDiagram.*;

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
public final class SpiderDiagramsReader {

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private SpiderDiagramsReader() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Reading Methods">
    /**
     * This method takes a string, parses it, and converts it to the internal
     * representation of spider diagrams (see {@link SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param input the textual representation of a spider diagram.
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     */
    public static SpiderDiagram readSpiderDiagram(String input) throws ReadingException {
        return readSpiderDiagram(new ANTLRStringStream(input));
    }

    /**
     * This method takes a {@link Reader}, parses it, and converts it to the
     * internal representation of spider diagrams (see {@link SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param reader the textual representation of a spider diagram.
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     * @throws IOException thrown if the input could not be read.
     */
    public static SpiderDiagram readSpiderDiagram(Reader reader) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRReaderStream(reader));
    }

    /**
     * This method takes an input stream, parses its contents, and converts it
     * to the internal representation of spider diagrams (see {@link
     * SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param input the textual representation of a spider diagram (a file input
     * stream stream or similar).
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     * @throws IOException thrown if the input could not be read.
     */
    public static SpiderDiagram readSpiderDiagram(InputStream input) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(input));
    }

    /**
     * This method takes an input stream, parses its contents, and converts it
     * to the internal representation of spider diagrams (see {@link
     * SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param input the textual representation of a spider diagram (a file input
     * stream stream or similar).
     * @param encoding the encoding of the input stream.
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     * @throws IOException thrown if the input could not be read.
     */
    public static SpiderDiagram readSpiderDiagram(InputStream input, String encoding) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRInputStream(input, encoding));
    }

    /**
     * This method takes an input stream, parses its contents, and converts it
     * to the internal representation of spider diagrams (see {@link
     * SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param inputFile a file containing the textual representation of a spider
     * diagram.
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     * @throws IOException thrown if the input could not be read.
     */
    public static SpiderDiagram readSpiderDiagram(File inputFile) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRFileStream(inputFile.getPath()));
    }

    /**
     * This method takes an input stream, parses its contents, and converts it
     * to the internal representation of spider diagrams (see {@link
     * SpiderDiagram}).
     * <p>The formal definition of the syntax can be found in
     * <a href="https://gitorious.org/speedith/speedith/blobs/master/devel/Speedith.Core/src/speedith/core/lang/reader/SpiderDiagrams.g">
     * the ANTLR grammar definition file</a>.</p>
     * @param inputFile a file containing the textual representation of a spider
     * diagram.
     * @param encoding the encoding of the input stream.
     * @return the internal representation of the spider diagram.
     * @throws ReadingException this exception is thrown if the textual
     * representation could not be translated or is malformed.
     * @throws IOException thrown if the input could not be read.
     */
    public static SpiderDiagram readSpiderDiagram(File inputFile, String encoding) throws ReadingException, IOException {
        return readSpiderDiagram(new ANTLRFileStream(inputFile.getPath(), encoding));
    }

    /**
     * Reads a region from the string.
     * <p>An example of a region:
     * <pre>[(["A", "B"], []), (["C"], ["D", "E"])]</pre>
     * </p>
     * @param input a region string.
     * @return the parsed and translated {@link Region region object}.
     * @throws ReadingException thrown if the input could not have been read.
     */
    public static Region readRegion(String input) throws ReadingException {
        return readElement(new ANTLRStringStream(input), new ElementReader<Region>() {

            @Override
            public Region readElement(SpiderDiagramsParser parser) throws ReadingException, RecognitionException {
                list_return list = parser.list();
                if (list == null || list.tree == null) {
                    throw new ReadingException(i18n("ERR_READING_INVALID_REGION"));
                }
                return new Region(ZoneTranslator.ZoneListTranslator.fromASTNode(list.tree));
            }
        });
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Translation Methods (from the AST to SpiderDiagrams)">
    private static SpiderDiagram readSpiderDiagram(CharStream chrStream) throws ReadingException {
        SpiderDiagramsLexer lexer = new SpiderDiagramsLexer(chrStream);
        SpiderDiagramsParser parser = new SpiderDiagramsParser(new CommonTokenStream(lexer));
        try {
            return toSpiderDiagram(parser.spiderDiagram());
        } catch (RecognitionException re) {
            throw new ReadingException(i18n("ERR_PARSE_INVALID_SYNTAX"), re);
        } catch (ParseException pe) {
            throw new ReadingException(pe.getMessage(), pe);
        }
    }

    private static interface ElementReader<T> {

        public T readElement(SpiderDiagramsParser parser) throws ReadingException, RecognitionException;
    }

    private static <T> T readElement(CharStream chrStream, ElementReader<T> elReader) throws ReadingException {
        SpiderDiagramsLexer lexer = new SpiderDiagramsLexer(chrStream);
        SpiderDiagramsParser parser = new SpiderDiagramsParser(new CommonTokenStream(lexer));
        try {
            return elReader.readElement(parser);
        } catch (RecognitionException re) {
            throw new ReadingException(i18n("ERR_PARSE_INVALID_SYNTAX"), re);
        } catch (ParseException pe) {
            throw new ReadingException(pe.getMessage(), pe);
        }
    }

    private static SpiderDiagram toSpiderDiagram(spiderDiagram_return spiderDiagram) throws ReadingException {
        if (spiderDiagram == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "spiderDiagram"));
        }
        return SDTranslator.Instance.fromASTNode(spiderDiagram.tree);
    }

    private abstract static class ElementTranslator<T> {

        public abstract T fromASTNode(CommonTree treeNode) throws ReadingException;
    }

    private static class ZoneTranslator extends ElementTranslator<Zone> {

        public static final ZoneTranslator Instance = new ZoneTranslator();
        public static final ListTranslator<Zone> ZoneListTranslator = new ListTranslator<>(Instance);
        private ListTranslator<ArrayList<String>> translator;

        private ZoneTranslator() {
            translator = new ListTranslator<>(SpiderDiagramsParser.SLIST, ListTranslator.StringListTranslator);
        }

        @Override
        public Zone fromASTNode(CommonTree treeNode) throws ReadingException {
            ArrayList<ArrayList<String>> inOutContours = translator.fromASTNode(treeNode);
            if (inOutContours == null || inOutContours.size() != 2) {
                throw new ReadingException(i18n("ERR_TRANSLATE_ZONE"), treeNode);
            }
            return new Zone(inOutContours.get(0), inOutContours.get(1));
        }
    }

    private static class HabitatTranslator extends ElementTranslator<Map<String, Region>> {

        public static final HabitatTranslator Instance = new HabitatTranslator();
        private ListTranslator<ArrayList<Object>> regionListTranslator;

        @SuppressWarnings("unchecked")
        private HabitatTranslator() {
            regionListTranslator = new ListTranslator<>(new TupleTranslator<>(new ElementTranslator<?>[]{StringTranslator.Instance, ZoneTranslator.ZoneListTranslator}));
        }

        @Override
        @SuppressWarnings("unchecked")
        public Map<String, Region> fromASTNode(CommonTree treeNode) throws ReadingException {
            ArrayList<ArrayList<Object>> rawHabitats = regionListTranslator.fromASTNode(treeNode);
            if (rawHabitats == null || rawHabitats.size() < 1) {
                return null;
            }
            HashMap<String, Region> habitats = new HashMap<>();
            for (ArrayList<Object> rawHabitat : rawHabitats) {
                if (rawHabitat.size() == 2) {
                    habitats.put((String) rawHabitat.get(0), new Region((ArrayList<Zone>) rawHabitat.get(1)));
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
            throw new ReadingException(i18n("ERR_TRANSLATE_INVALID_STRING"), treeNode);
        }
    }

    private static class IDTranslator extends ElementTranslator<String> {

        public static final IDTranslator Instance = new IDTranslator();

        @Override
        public String fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == SpiderDiagramsParser.ID) {
                return treeNode.token.getText();
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_INVALID_ID"), treeNode);
        }
    }

    private static abstract class GeneralSDTranslator<V extends SpiderDiagram> extends ElementTranslator<V> {

        private GeneralMapTranslator<Object> keyValueMapTranslator;
        private TreeSet<String> mandatoryAttributes;

        private GeneralSDTranslator(int headTokenType) {
            keyValueMapTranslator = new GeneralMapTranslator<>(headTokenType, new HashMap<String, ElementTranslator<? extends Object>>(), null);
        }

         <T> void addMandatoryAttribute(String key, ElementTranslator<T> valueTranslator) {
            if (mandatoryAttributes == null) {
                mandatoryAttributes = new TreeSet<>();
            }
            mandatoryAttributes.add(key);
            keyValueMapTranslator.typedValueTranslators.put(key, valueTranslator);
        }

         <T> void addOptionalAttribute(String key, ElementTranslator<T> valueTranslator) {
            keyValueMapTranslator.typedValueTranslators.put(key, valueTranslator);
        }

         <T> void addDefaultAttribute(ElementTranslator<T> valueTranslator) {
            keyValueMapTranslator.defaultValueTranslator = valueTranslator;
        }

        private boolean areMandatoryPresent(Map<String, ? extends Object> attributes) {
            if (mandatoryAttributes != null) {
                for (String string : mandatoryAttributes) {
                    if (!attributes.containsKey(string)) {
                        return false;
                    }
                }
            }
            return true;
        }

        @Override
        public V fromASTNode(CommonTree treeNode) throws ReadingException {
            Map<String, Entry<Object, CommonTree>> attrs = keyValueMapTranslator.fromASTNode(treeNode);
            if (areMandatoryPresent(attrs)) {
                return createSD(attrs, treeNode);
            } else {
                throw new ReadingException(i18n("ERR_TRANSLATE_MISSING_ELEMENTS", keyValueMapTranslator.typedValueTranslators.keySet()), treeNode);
            }
        }

        abstract V createSD(Map<String, Entry<Object, CommonTree>> attributes, CommonTree mainNode) throws ReadingException;
    }

    private static class SDTranslator extends ElementTranslator<SpiderDiagram> {

        public static final SDTranslator Instance = new SDTranslator();

        private SDTranslator() {
        }

        @Override
        public SpiderDiagram fromASTNode(CommonTree treeNode) throws ReadingException {
            switch (treeNode.token.getType()) {
                case SpiderDiagramsParser.SD_BINARY:
                    return CompoundSDTranslator.BinaryTranslator.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_UNARY:
                    return CompoundSDTranslator.UnaryTranslator.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_COMPOUND:
                    return CompoundSDTranslator.CompoundTranslator.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_PRIMARY:
                    return PrimarySDTranslator.Instance.fromASTNode(treeNode);
                case SpiderDiagramsParser.SD_NULL:
                    return NullSDTranslator.Instance.fromASTNode(treeNode);
                default:
                    throw new ReadingException(i18n("ERR_UNKNOWN_SD_TYPE"));
            }
        }
    }

    private static class CompoundSDTranslator extends GeneralSDTranslator<CompoundSpiderDiagram> {

        public static final CompoundSDTranslator CompoundTranslator = new CompoundSDTranslator(SpiderDiagramsParser.SD_COMPOUND);
        public static final CompoundSDTranslator BinaryTranslator = new CompoundSDTranslator(SpiderDiagramsParser.SD_BINARY);
        public static final CompoundSDTranslator UnaryTranslator = new CompoundSDTranslator(SpiderDiagramsParser.SD_UNARY);

        public CompoundSDTranslator(int headTokenType) {
            super(headTokenType);
            addMandatoryAttribute(SDTextOperatorAttribute, StringTranslator.Instance);
            addDefaultAttribute(SDTranslator.Instance);
        }

        @Override
        CompoundSpiderDiagram createSD(Map<String, Entry<Object, CommonTree>> attributes, CommonTree mainNode) throws ReadingException {
            String operator = (String) attributes.remove(SDTextOperatorAttribute).getKey();
            ArrayList<SpiderDiagram> operands = new ArrayList<>();
            int i = 1;
            Entry<Object, CommonTree> curSD, lastSD = null;
            while ((curSD = attributes.remove(CompoundSpiderDiagram.SDTextArgAttribute + i++)) != null && curSD.getKey() instanceof SpiderDiagram) {
                operands.add((SpiderDiagram) curSD.getKey());
                lastSD = curSD;
            }
            if (curSD != null) {
                throw new ReadingException(i18n("GERR_ILLEGAL_STATE"), (CommonTree) curSD.getValue().getChild(0));
            }
            if (!attributes.isEmpty()) {
                throw new ReadingException(i18n("ERR_TRANSLATE_UNKNOWN_ATTRIBUTES", attributes.keySet()), (CommonTree) attributes.values().iterator().next().getValue().getChild(0));
            }
            try {
                return SpiderDiagrams.createCompoundSD(operator, operands, false);
            } catch (Exception e) {
                throw new ReadingException(e.getLocalizedMessage(), lastSD == null ? mainNode : (CommonTree) lastSD.getValue().getChild(0));
            }
        }
    }

    private static class PrimarySDTranslator extends GeneralSDTranslator<PrimarySpiderDiagram> {

        public static final PrimarySDTranslator Instance = new PrimarySDTranslator();

        private PrimarySDTranslator() {
            super(SpiderDiagramsParser.SD_PRIMARY);
            addMandatoryAttribute(SDTextSpidersAttribute, ListTranslator.StringListTranslator);
            addMandatoryAttribute(SDTextHabitatsAttribute, HabitatTranslator.Instance);
            addMandatoryAttribute(SDTextShadedZonesAttribute, new ListTranslator<>(ZoneTranslator.Instance));
            addOptionalAttribute(SDTextPresentZonesAttribute, new ListTranslator<>(ZoneTranslator.Instance));
        }

        @Override
        @SuppressWarnings("unchecked")
        PrimarySpiderDiagram createSD(Map<String, Entry<Object, CommonTree>> attributes, CommonTree mainNode) throws ReadingException {
            Entry<Object, CommonTree> presentZonesAttribute = attributes.get(SDTextPresentZonesAttribute);
            return SpiderDiagrams.createPrimarySDNoCopy((Collection<String>) attributes.get(SDTextSpidersAttribute).getKey(),
                    (Map<String, Region>) attributes.get(SDTextHabitatsAttribute).getKey(),
                    (Collection<Zone>) attributes.get(SDTextShadedZonesAttribute).getKey(),
                    presentZonesAttribute == null ? null : (Collection<Zone>) presentZonesAttribute.getKey());
        }
    }

    private static class NullSDTranslator extends GeneralSDTranslator<NullSpiderDiagram> {

        public static final NullSDTranslator Instance = new NullSDTranslator();

        private NullSDTranslator() {
            super(SpiderDiagramsParser.SD_NULL);
        }

        @Override
        NullSpiderDiagram createSD(Map<String, Entry<Object, CommonTree>> attributes, CommonTree mainNode) throws ReadingException {
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
                checkNode(treeNode);
                if (treeNode.getChildCount() < 1) {
                    return null;
                }
                ArrayList<V> objs = new ArrayList<>(treeNode.getChildCount());
                int i = 0;
                for (Object obj : treeNode.getChildren()) {
                    objs.add(fromASTChildAt(i++, (CommonTree) obj));
                }
                return objs;
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n(i18n("ERR_TRANSLATE_LIST_OR_SLIST"))), treeNode);
        }

        protected abstract V fromASTChildAt(int i, CommonTree treeNode) throws ReadingException;

        /**
         * Checks whether the node (which should be a list) is okay for
         * translation. It indicates so by not throwing an exception.
         * <p>The default implementation does nothing.</p>
         * @param treeNode the node which should be checked.
         * @exception ReadingException this exception should be thrown if the
         * AST node is not valid in some sense.
         */
        protected void checkNode(CommonTree treeNode) throws ReadingException {
        }
    }

    private static class ListTranslator<V> extends CollectionTranslator<V> {

        public static final ListTranslator<String> StringListTranslator = new ListTranslator<>(StringTranslator.Instance);
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
                throw new ReadingException(i18n("ERR_TRANSLATE_TOO_MANY_ELMNTS"), treeNode);
            }
            return valueTranslators.get(i).fromASTNode(treeNode);
        }

        @Override
        protected void checkNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.getChildCount() != valueTranslators.size()) {
                throw new ReadingException(i18n("ERR_TRANSLATE_ELEMENTS_COUNT", valueTranslators.size(), treeNode.getChildCount()), treeNode);
            }
        }
    }

    private static class GeneralMapTranslator<V> extends ElementTranslator<Map<String, Entry<V, CommonTree>>> {

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
        public Map<String, Entry<V, CommonTree>> fromASTNode(CommonTree treeNode) throws ReadingException {
            if (treeNode.token != null && treeNode.token.getType() == headTokenType) {
                if (treeNode.getChildCount() < 1) {
                    return null;
                }
                HashMap<String, Entry<V, CommonTree>> kVals = new HashMap<>();
                for (Object obj : treeNode.getChildren()) {
                    CommonTree node = (CommonTree) obj;
                    if (node.token != null && node.token.getType() == SpiderDiagramsParser.PAIR && node.getChildCount() == 2) {
                        String key = IDTranslator.Instance.fromASTNode((CommonTree) node.getChild(0));
                        ElementTranslator<? extends V> translator = null;
                        if (typedValueTranslators != null) {
                            translator = typedValueTranslators.get(key);
                        }
                        if (translator == null) {
                            if (defaultValueTranslator != null) {
                                translator = defaultValueTranslator;
                            } else {
                                throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_KEY_VALUE", key, typedValueTranslators == null ? "" : typedValueTranslators.keySet()), (CommonTree) node.getChild(0));
                            }
                        }
                        V value = translator.fromASTNode((CommonTree) node.getChild(1));
                        kVals.put(key, new SimpleEntry<>(value, node));
                    } else {
                        throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n("TRANSLATE_KEY_VALUE_PAIR")), node);
                    }
                }
                return kVals;
            }
            throw new ReadingException(i18n("ERR_TRANSLATE_UNEXPECTED_ELEMENT", i18n(i18n("ERR_TRANSLATE_LIST_OR_SLIST"))), treeNode);
        }
    }
    // </editor-fold>
}
