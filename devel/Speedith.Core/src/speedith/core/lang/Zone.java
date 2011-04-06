/*
 *   Project: Speedith.Core
 * 
 * File name: Zone.java
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
import java.util.Collections;
import java.util.SortedSet;
import java.util.TreeSet;
import speedith.core.util.SortedSets;
import static speedith.core.i18n.Translations.i18n;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Zone implements Comparable<Zone> {

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private TreeSet<String> inContours;
    private TreeSet<String> outContours;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new zone and initialises it with the two given collections of
     * contour names.
     * @param inContours the collection of names of contours which contain this
     * new zone.
     * <p>Note that duplicated contour names will be ignored.</p>
     * @param outContours the collection of names of contours which lie entirely
     * outside this new zone.
     * <p>Note that duplicated contour names will be ignored.</p>
     */
    public Zone(Collection<String> inContours, Collection<String> outContours) {
        this.inContours = inContours == null ? null : new TreeSet<String>(inContours);
        this.outContours = outContours == null ? null : new TreeSet<String>(outContours);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns a read-only set of contour names.
     * <p>These are the contours that contain this zone.</p>
     * <p>Note: this method may return {@code null}, which indicates that this
     * zone is contained in no contour.</p>
     * @return a read-only set of contour names.
     * <p>These are the contours that contain this zone.</p>
     */
    public SortedSet<String> getInContours() {
        return inContours == null ? null : Collections.unmodifiableSortedSet(inContours);
    }

    /**
     * Returns a read-only set of contour names.
     * <p>These are the contours that lie outside this zone.</p>
     * <p>Note: this method may return {@code null}, which indicates that this
     * zone does not lie outside any contour.</p>
     * @return a read-only set of contour names.
     * <p>These are the contours that lie outside this zone.</p>
     */
    public SortedSet<String> getOutContours() {
        return outContours == null ? null : Collections.unmodifiableSortedSet(outContours);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Compares (lexicographically) this zone to another and returns {@code -1},
     * {@code 0}, or {@code 1} if this zone is alphabetically smaller, equal, or
     * larger (respectively) than the other zone.
     * <p>This function should be used to order zones alphabetically.</p>
     * <p>Note: this method uses the
     * {@link SortedSets#compareNaturally(java.util.SortedSet, java.util.SortedSet) }
     * method internally (to compare the contour names with each other).</p>
     * @param other the other zone with which to compare this one.
     * @return {@code -1}, {@code 0}, or {@code 1} if this zone is
     * alphabetically smaller, equal, or larger (respectively) than the other
     * zone.
     */
    public int compareTo(Zone other) {
        if (other == null) {
            throw new NullPointerException();
        }
        if (this == other) {
            return 0;
        } else {
            int retVal = SortedSets.compareNaturally(inContours, other.inContours);
            if (retVal == 0) {
                retVal = SortedSets.compareNaturally(outContours, other.outContours);
            }
            return retVal;
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        sb.append('(');
        SpiderDiagram.printStringList(sb, inContours);
        sb.append(", ");
        SpiderDiagram.printStringList(sb, outContours);
        sb.append(')');
    }
    // </editor-fold>
}
