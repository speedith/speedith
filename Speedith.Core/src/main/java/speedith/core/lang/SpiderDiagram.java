/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderDiagram.java
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
package speedith.core.lang;

import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import static speedith.core.i18n.Translations.i18n;

/**
 * This is the base class of all data structures which contain information about
 * particular spider diagrams. <p><span style="font-weight:bold">Note</span>:
 * all spider diagram instances and their sub-components are immutable.</p>
 * <p>You can construct new spider diagrams via the static methods in {@link
 * SpiderDiagrams}.</p> <p>Instances of this class (and its derived classes) are
 * immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SpiderDiagram implements Iterable<SpiderDiagram>, SpiderDiagramElement {

    // <editor-fold defaultstate="collapsed" desc="Public Methods">

    /**
     * Compares this spider diagram with another and returns {@code true} iff
     * they are equivalent up to spider renaming and region reordering.
     * <p/>
     * <p>The default implementation of this
     * method simply calls the {@link
     * SpiderDiagram#equals(java.lang.Object) syntactical equality method}.</p>
     * <p/>
     * <p>If this method returns {@code true} then this spider diagram equals
     * semantically to the other. However, if this method returns {@code false}
     * it does not mean anything.</p>
     *
     * @param other the other spider diagram to compare this one against.
     * @return {@code true} if the semantic equivalence could have been
     *         established. Otherwise it returns {@code false}.
     */
    public boolean isSEquivalentTo(SpiderDiagram other) {
        return equals(other);
    }

    /**
     * Compares this spider diagram with another and returns {@code true} iff
     * they are syntactically the same. <p>If this method returns {@code true}
     * then this spider diagram is semantically equivalent to the compared
     * one.</p> <p>For two spider diagrams to be syntactically equivalent, they
     * have to conform to the following criteria: <ul> <li>any {@link NullSpiderDiagram}
     * instance equals to another {@link
     * NullSpiderDiagram} instance (in fact, the {@link
     * NullSpiderDiagram} is a singleton),</li> <li>an instance of an {@link CompoundSpiderDiagram}
     * equals to another if: <ul> <li>both have the same operator (an equality
     * comparison on {@link CompoundSpiderDiagram#getOperator()}) and</li>
     * <li>both have the same operands (an equality comparison on all {@link CompoundSpiderDiagram#getOperands()}).</li>
     * </ul> </li> <li>a {@link PrimarySpiderDiagram} equals (syntactically) to
     * another iff: <ul> <li>they have the same {@link PrimarySpiderDiagram#getSpiders()
     * spiders},</li> <li>they have the same {@link PrimarySpiderDiagram#getShadedZones()
     * shaded zones}, and</li> <li>they have the same {@link PrimarySpiderDiagram#getHabitats()
     * habitats}.</li> </ul> <span style="font-weight:bold">Note</span>: the
     * above <span style="font-style:italic;">collection comparisons</span> are
     * all element-wise equality comparisons. </li> </ul> </p>
     *
     * @param other the other spider diagram to compare this one against.
     * @return {@code true} iff the two spider diagrams are syntactically the
     *         same.
     */
    @Override
    public abstract boolean equals(Object other);

    /**
     * All spider diagrams should produce a hash code that conforms the
     * following semantics: let <span style="font-style:italic;">A</span> and
     * <span style="font-style:italic;">B</span> be two spider diagrams, then if
     * <span style="font-style:italic;">A</span>{@code .equals(}<span style="font-style:italic;">B</span>{@code)},
     * then <span style="font-style:italic;">A</span>{@code .hashCode() ==
     * }<span style="font-style:italic;">B</span>{@code .hashCode()}.
     *
     * @return an integer satisfying the <span style="font-style:italic;">hash
     *         property</span>.
     */
    @Override
    public abstract int hashCode();

    /**
     * Visits the given spider diagram and its children in a parent-first left-
     * to-right order. <p>If the diagram does not have any parents, then the
     * transformer will get an empty or a {@code null} stack of parents.</p>
     * <p>By default, this method calls the overloaded {@link
     * SpiderDiagram#transform(speedith.core.lang.Transformer, boolean)} method
     * with parent tracking enabled. This means that the parents of sub-diagrams
     * will be available to the transformer (the immediate parent of the current
     * spider diagram is the first element of the list - this is due to how the
     * {@link LinkedList#push(java.lang.Object) push method} in the linked list
     * works).</p> <p>Note: this function does not descend into spider diagrams
     * returned by the given {@link Transformer transformer}.</p>
     *
     * @param t the object that transforms particular sub-diagrams.
     * @return the transformed spider diagram.
     */
    public SpiderDiagram transform(Transformer t) {
        return transform(t, true);
    }

    /**
     * Visits the given spider diagram and its children in a parent-first left-
     * to-right order. <p>If the diagram does not have any parents, then the
     * transformer will get an empty or a {@code null} stack of parents.</p>
     * <p>Note: this function does not descend into spider diagrams returned by
     * the given {@link Transformer transformer}.</p>
     *
     * @param t            the object that transforms particular sub-diagrams.
     * @param trackParents indicates whether the parents of the visited
     *                     sub-diagrams should be tracked. If this parameter is set to {@code false}
     *                     then the transformer's {@link Transformer#transform(speedith.core.lang.CompoundSpiderDiagram, int, int, java.util.LinkedList)
     *                     transform methods} will be called with the parent stack set to {@code
     *                     null}.
     * @return the transformed spider diagram.
     */
    public abstract SpiderDiagram transform(Transformer t, boolean trackParents);

    /**
     * Visits every sub-diagram in this diagram and calls the appropriate
     * methods of the given {@link DiagramVisitor visitor}. <p>This method
     * simply calls the {@link SpiderDiagram#visit(speedith.core.lang.DiagramVisitor, boolean) full visit}
     * function with parent tracking enabled.</p>
     *
     * @param <T>     the type of the result produced by the visitor.
     * @param visitor the object that will receive calls upon visiting
     *                particular elements.
     * @return the result produced by the visitor.
     */
    public <T> T visit(DiagramVisitor<T> visitor) {
        return visit(visitor, true);
    }

    /**
     * Visits every sub-diagram in this diagram and calls the appropriate
     * methods of the given {@link DiagramVisitor visitor}.
     *
     * @param <T>          the type of the result produced by the visitor.
     * @param visitor      the object that will receive calls upon visiting
     *                     particular elements.
     * @param trackParents indicates whether the parents of the visited
     *                     sub-diagrams should be tracked. If this parameter is set to {@code false}
     *                     then the visitor's {@link DiagramVisitor#visit(speedith.core.lang.SpiderDiagram, int, int, java.util.LinkedList)
     *                     visit method} will be called with the parent stack set to {@code
     *                     null}.
     * @return the result produced by the visitor.
     */
    public <T> T visit(DiagramVisitor<T> visitor, boolean trackParents) {
        if (visitor == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "visitor"));
        }
        visitor.init(this);
        if (!visitor.isDone()) {
            visitor.visit(
                    this,
                    0,
                    trackParents ? new ArrayList<CompoundSpiderDiagram>() : null,
                    trackParents ? new ArrayList<Integer>() : null,
                    trackParents ? new ArrayList<Integer>() : null
            );
        }
        visitor.end();
        return visitor.getResult();
    }

    /**
     * Returns the spider sub-diagram at the given index within this spider
     * diagram. <p>This index indicates the number of appearance (from left to
     * right) of a sub-diagram within this compound diagram.</p> <p>See {@link SubDiagramIndexArg}
     * for more info on the <span style="font-style:italic;">diagram
     * indices</span>.</p> <p>Note that the {@link PrimarySpiderDiagram primary}
     * and {@link
     * NullSpiderDiagram null} spider diagrams do not have any sub-diagrams.</p>
     *
     * @param index the index of the spider sub-diagram in this spider diagram
     *              to return.
     * @return the spider sub-diagram at the given index (as it appears in this
     *         spider diagram from left to right).
     */
    public abstract SpiderDiagram getSubDiagramAt(int index);

    /**
     * Returns the number of all sub-diagrams in this diagram (counting all the
     * children of the children and also counting the diagram itself).
     *
     * @return the number of all sub-diagrams in this diagram (counting all the
     *         children of the children and also counting the diagram itself).
     */
    public abstract int getSubDiagramCount();

    /**
     * Returns the first index of the given spider diagram.
     *
     * @param sd the sub-diagram for which we want to look up the index
     * @return the first index of the given spider diagram.
     */
    public int getSubDiagramIndex(final SpiderDiagram sd) {
        Integer index = this.visit(new DiagramVisitor<Integer>() {

            private int foundIndex = -1;

            @Override
            public void init(SpiderDiagram root) {
            }

            @Override
            public void end() {
            }

            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagram.equals(sd)) {
                    foundIndex = subDiagramIndex;
                }
            }

            @Override
            public boolean isDone() {
                return foundIndex != -1;
            }

            @Override
            public Integer getResult() {
                return foundIndex;
            }
        }, false);
        return index;
    }

    /**
     * Checks whether this spider diagram is valid (whether it conforms to all
     * constraints of a well-defined spider diagram). <p>A spider diagram is
     * valid if: <ul> <li>the sets of in- and out-contours are disjoint,</li>
     * <li>all zones are fully specified (they contain all the contours that are
     * mentioned in the primary spider diagram), and</li> <li>all operands in a
     * compound spider diagram are valid.</li> </ul> </p>
     *
     * @return {@code true} if and only if the diagram is valid according to the
     *         above rules.
     */
    public abstract boolean isValid();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">

    /**
     * Converts this spider diagram to its textual representation (see {@link speedith.core.lang.reader.SpiderDiagramsReader#readSpiderDiagram(java.lang.String)}
     * for an explanation on how to read spider diagrams from this textual
     * representation.
     */
    @Override
    public abstract String toString();

    /**
     * Converts this spider diagram to its textual representation (see {@link speedith.core.lang.reader.SpiderDiagramsReader#readSpiderDiagram(java.lang.String)}
     * for an explanation on how to read spider diagrams from this textual
     * representation.
     *
     * @param sb the string builder into which to put the textual representation
     *           of this spider diagram (must not be {@code null}).
     * @throws IOException thrown if the string builder throws an exception.
     */
    public abstract void toString(Appendable sb) throws IOException;

    static void printString(Appendable sb, String str) throws IOException {
        sb.append('"').append(str).append('"');
    }

    static void printStringList(Appendable sb, Collection<String> strList) throws IOException {
        sb.append('[');
        if (strList != null) {
            Iterator<String> strIter = strList.iterator();
            if (strIter.hasNext()) {
                sb.append('"').append(strIter.next()).append('"');
                while (strIter.hasNext()) {
                    printString(sb.append(", "), strIter.next());
                }
            }
        }
        sb.append(']');
    }

    static void printZoneList(Appendable sb, Collection<Zone> zones) throws IOException {
        sb.append('[');
        if (zones != null) {
            Iterator<Zone> spIterator = zones.iterator();
            if (spIterator.hasNext()) {
                spIterator.next().toString(sb);
                while (spIterator.hasNext()) {
                    spIterator.next().toString(sb.append(", "));
                }
            }
        }
        sb.append(']');
    }

    public int getParentIndexOf(final int childIndex) {
        return visit(new DiagramVisitor<Integer>() {
            private static final int PARENT_NOT_YET_NDETERMINED = -2;
            private static final int HAS_NO_PARENT = -1;
            public int parentIndex = PARENT_NOT_YET_NDETERMINED;

            @Override
            public void init(SpiderDiagram root) {
            }

            @Override
            public void end() {
            }

            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == childIndex) {
                    if (parents == null || parents.size() < 1) {
                        parentIndex = HAS_NO_PARENT;
                    } else {
                        parentIndex = parentIndices.get(parentIndices.size() - 1);
                    }
                }
            }

            @Override
            public boolean isDone() {
                return parentIndex != PARENT_NOT_YET_NDETERMINED;
            }

            @Override
            public Integer getResult() {
                return parentIndex;
            }
        });
    }
    // </editor-fold>
}
