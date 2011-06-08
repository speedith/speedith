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

import java.util.Collection;
import java.util.Iterator;

/**
 * This is the base class of all data structures which contain information about
 * particular spider diagrams.
 * <p><span style="font-weight:bold">Note</span>: all spider diagram instances
 * and their sub-components are immutable.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SpiderDiagram {
    
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Compares this spider diagram with another and returns {@code true} iff
     * they are syntactically the same.
     * <p>If this method returns {@code true} then this spider diagram is
     * semantically equivalent to the compared one.</p>
     * <p>For two spider diagrams to be syntactically equivalent, they have to
     * conform to the following criteria:
     *  <ul>
     *      <li>any {@link NullSpiderDiagram} instance equals to another {@link
     *          NullSpiderDiagram} instance (in fact, the {@link
     *          NullSpiderDiagram} is a singleton),</li>
     *      <li>an instance of an {@link NarySpiderDiagram} equals to another
     *          if:
     *          <ul>
     *              <li>both have the same operator (an equality comparison
     *              on {@link NarySpiderDiagram#getOperator()}) and</li>
     *              <li>both have the same operands (an equality comparison
     *              on all {@link NarySpiderDiagram#getOperands()}).</li>
     *          </ul>
     *      </li>
     *      <li>a {@link PrimarySpiderDiagram} equals (syntactically) to another
     *          iff:
     *          <ul>
     *              <li>they have the same {@link PrimarySpiderDiagram#getSpiders()
     *          spiders},</li>
     *              <li>they have the same {@link PrimarySpiderDiagram#getShadedZones()
     *                  shaded zones}, and</li>
     *              <li>they have the same {@link PrimarySpiderDiagram#getHabitats()
     *                  habitats}.</li>
     *          </ul>
     *          Note that the above <span style="font-style:italic;">collection
     *          comparisons</span> are element-wise equality comparisons.
     *      </li>
     *  </ul>
     * </p>
     * @param other
     * @return
     */
    public abstract boolean equals(SpiderDiagram other);
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    /**
     * Converts this spider diagram to its textual representation (see {@link speedith.core.lang.reader.SpiderDiagramsReader#readSpiderDiagram(java.lang.String)}
     * for an explanation on how to read spider diagrams from this textual representation.
     */
    @Override
    public abstract String toString();

    /**
     * Converts this spider diagram to its textual representation (see {@link speedith.core.lang.reader.SpiderDiagramsReader#readSpiderDiagram(java.lang.String)}
     * for an explanation on how to read spider diagrams from this textual representation.
     * @param sb the string builder into which to put the textual representation
     * of this spider diagram (must not be {@code null}).
     */
    public abstract void toString(StringBuilder sb);

    static void printString(StringBuilder sb, String str) {
        sb.append('"').append(str).append('"');
    }

    static void printStringList(StringBuilder sb, Collection<String> strList) {
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

    static void printZoneList(StringBuilder sb, Collection<Zone> zones) {
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
    // </editor-fold>
}
