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

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.SortedSet;
import java.util.TreeSet;
import javax.naming.OperationNotSupportedException;
import speedith.core.util.Sets;
import static speedith.core.i18n.Translations.i18n;
import static speedith.core.util.Sets.equal;

/**
 * Represents a zone from the theory of spider diagrams.
 * <p>For more information see
 * <a href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924" title="10.1112/S1461157000000942">
 * Spider Diagrams (2005)</a>.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Zone implements Comparable<Zone> {

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private TreeSet<String> inContours;
    private TreeSet<String> outContours;
    private boolean hashInvalid = true;
    private int hash;
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
        this(inContours == null ? null : new TreeSet<String>(inContours),
                outContours == null ? null : new TreeSet<String>(outContours));
    }

    /**
     * Creates a new zone and initialises it with the two given collections of
     * contour names.
     * <p><span style="font-weight:bold">Important</span>: this method does
     * not make a copy of the given in- and out- contour sets. With this, one
     * can violate the immutability property of this class (which means that the
     * contract for the {@link Zone#hashCode()} method might be broken). So,
     * make sure that you do not change the given sets after creating this zone
     * with them.</p>
     * @param inContours the collection of names of contours which contain this
     * new zone.
     * <p>Note that duplicated contour names will be ignored.</p>
     * @param outContours the collection of names of contours which lie entirely
     * outside this new zone.
     * <p>Note that duplicated contour names will be ignored.</p>
     */
    Zone(TreeSet<String> inContours, TreeSet<String> outContours) {
        this.inContours = inContours;
        this.outContours = outContours;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns a read-only set of contour names.
     * <p>These are the contours that contain this zone.</p>
     * <p>Note: this method may return {@code null}, which indicates that this
     * zone is contained in no contour.</p>
     * @return a read-only set of contour names.
     * <p>These are the contours that contain this zone.</p>
     */
    public SortedSet<String> getInContours() {
        return inContours == null || inContours.isEmpty() ? null : Collections.unmodifiableSortedSet(inContours);
    }

    /**
     * Returns the number of {@link Zone#getInContours() in-contours}.
     * @return the number of {@link Zone#getInContours() in-contours}.
     */
    public int getInContoursCount() {
        return inContours == null ? 0 : inContours.size();
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
        return outContours == null || outContours.isEmpty() ? null : Collections.unmodifiableSortedSet(outContours);
    }

    /**
     * Returns the number of {@link Zone#getOutContours() out-contours}.
     * @return the number of {@link Zone#getOutContours() out-contours}.
     */
    public int getOutContoursCount() {
        return outContours == null ? 0 : outContours.size();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Compares (lexicographically) this zone to another and returns {@code -1},
     * {@code 0}, or {@code 1} if this zone is alphabetically smaller, equal, or
     * larger (respectively) than the other zone.
     * <p>This function should be used to order zones alphabetically.</p>
     * <p>Note: this method uses the
     * {@link Sets#compareNaturally(java.util.SortedSet, java.util.SortedSet) }
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
            int retVal = Sets.compareNaturally(inContours, other.inContours);
            if (retVal == 0) {
                retVal = Sets.compareNaturally(outContours, other.outContours);
            }
            return retVal;
        }
    }

    /**
     * Two zones are equal if they have exactly the same {@link
     * Zone#getInContours() in countours} and {@link Zone#getOutContours() out
     * countours}.
     * @param obj the object with which to compare this zone.
     * @return {@code true} if and only if {@code obj} is a region and it has
     * exactly the same {@link Zone#getInContours() in countours} and {@link
     * Zone#getOutContours() out countours}.
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof Zone) {
            Zone other = (Zone) obj;
            return equal(inContours, other.inContours) && equal(outContours, other.outContours);
        }
        return false;
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = (inContours == null || inContours.isEmpty() ? 0 : inContours.hashCode())
                    + (outContours == null || outContours.isEmpty() ? 0 : outContours.hashCode());
            hashInvalid = false;
        }
        return hash;
    }

    /**
     * Takes this zone and creates a copy of it with in-contours replaced with
     * the given ones.
     * @param inContours the in-contours to put into the new zone.
     * @return a copy of this zone with in-contours replaced with the given
     * ones.
     */
    public Zone withInContours(String... inContours) {
        return new Zone(inContours == null ? null : new TreeSet<String>(Arrays.asList(inContours)), this.outContours);
    }

    /**
     * Takes this zone and creates a copy of it with out-contours replaced with
     * the given ones.
     * @param outContours the out-contours to put into the new zone.
     * @return a copy of this zone with out-contours replaced with the given
     * ones.
     */
    public Zone withOutContours(String... outContours) {
        return new Zone(this.inContours, outContours == null ? null : new TreeSet<String>(Arrays.asList(outContours)));
    }

    /**
     * Creates a new zone with the given in-contours only (no out-contours).
     * @param inContours the in-contours to put into the new zone.
     * @return a new zone with the given in-contours only (no out-contours).
     */
    public static Zone fromInContours(String... inContours) {
        return new Zone(Arrays.asList(inContours), null);
    }

    /**
     * Creates a new zone with the given out-contours only (no in-contours).
     * @param outContours the in-contours to put into the new zone.
     * @return a new zone with the given out-contours only (no in-contours).
     */
    public static Zone fromOutContours(String... outContours) {
        return new Zone(null, Arrays.asList(outContours));
    }

    /**
     * Checks whether this zone contains all the contours (either as in- or out-
     * contours).
     * <p>This method also checks whether the set of in- and out- contours are
     * disjoint.</p>
     * @param contours the set of contours against which to validate this zone.
     * @return {@code true} if and only if this zone has:
     * <ul>
     *      <li>disjoint in- and out-contours sets, and</li>
     *      <li>contains all the contours.</li>
     * </ul>
     */
    public boolean isValid(SortedSet<String> contours) {
        throw new UnsupportedOperationException();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    /**
     * Puts the string representation of this zone into the provided string
     * builder.
     * @param sb the string builder into which to write the string representation
     * of this zone.
     */
    public void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        sb.append('(');
        SpiderDiagram.printStringList(sb, inContours);
        sb.append(", ");
        SpiderDiagram.printStringList(sb, outContours);
        sb.append(')');
    }
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(sb);
        return sb.toString();
    }
    // </editor-fold>
}
