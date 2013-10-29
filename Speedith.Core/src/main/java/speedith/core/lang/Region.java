/*
 *   Project: Speedith.Core
 * 
 * File name: Region.java
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

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.SortedSet;
import java.util.TreeSet;
import propity.util.Sets;
import static speedith.core.i18n.Translations.i18n;

/**
 * This class represents a region in spider diagrams. <p>A region is a union of
 * zones. Thus the {@link Region} class contains
 * {@link Region#getZones() a set of zones} which constitute it.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Region implements Comparable<Region>, SpiderDiagramElement {

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private final TreeSet<Zone> zones;
    private boolean hashInvalid = true;
    private int hash;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new region from the given collection of zones. The resulting
     * region will constitute of these zones. <p>Note that duplicate zones in
     * the given collection will be ignored.</p>
     *
     * @param zones the collection of zones from which to construct this region.
     * <p>This argument may be {@code null}. This indicates an empty region.</p>
     */
    public Region(Collection<Zone> zones) {
        this(zones == null ? null : new TreeSet<Zone>(zones));
    }

    /**
     * Creates a new region from the given collection of zones. The resulting
     * region will constitute of these zones. <p>Note that duplicate zones in
     * the given collection will be ignored.</p>
     *
     * @param zones the collection of zones from which to construct this region.
     * <p>This argument may be {@code null}. This indicates an empty region.</p>
     */
    public Region(Zone... zones) {
        this(zones == null ? null : new TreeSet<Zone>(Arrays.asList(zones)));
    }

    /**
     * Creates a new region from the given collection of zones. The resulting
     * region will constitute of these zones. <p><span
     * style="font-weight:bold">Important</span>: this method does not make a
     * copy of the given zone set. Hence, it is possible to violate the
     * immutability property of this class (which means that the contract for
     * the {@link Zone#hashCode()} method might be broken). So, make sure that
     * you do not change the given set after creating this region with it.</p>
     * <p>Note that duplicate zones in the given collection will be ignored.</p>
     *
     * @param zones the collection of zones from which to construct this region.
     * <p>This argument may be {@code null}. This indicates an empty region.</p>
     */
    public Region(TreeSet<Zone> zones) {
        this.zones = zones;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns a set of {@link Zone zones} which make up this region. <p>Note:
     * this method may return {@code null}, which indicates an empty region.</p>
     *
     * @return a set of {@link Zone zones} which make up this region. <p>Note:
     * this method may return {@code null}, which indicates an empty region.</p>
     */
    public SortedSet<Zone> getZones() {
        return zones == null || zones.isEmpty() ? null : Collections.unmodifiableSortedSet(zones);
    }

    /**
     * Returns the number of {@link Region#getZones() zones} in this region.
     *
     * @return the number of {@link Region#getZones() zones} in this region.
     */
    public int getZonesCount() {
        return zones == null ? 0 : zones.size();
    }

    /**
     * Returns {@code true} iff the given zone is within the set of zones of
     * this region.
     * 
     * @param z
     * @return {@code true} iff the given zone is within the set of zones of
     * this region.
     */
    boolean contains(Zone z) {
        return zones != null && zones.contains(z);
    }

    /**
     * Returns {@code true} iff this region is contained within the other
     * region.
     *
     * @param other the other region.
     * @return {@code true} iff this region is contained within the other
     * region.
     */
    public boolean isSubregionOf(Region other) {
        return Sets.isNaturalSubset(zones, other.zones);
    }

    /**
     * Creates a new region made only of zones that are contained by this one
     * and not by the other. <p>This method does not change the current region.
     * It returns a new one.</p>
     *
     * @param other the other region to subtract from this one.
     * @return a new region made only of zones that are contained by this one
     * and not by the other.
     */
    public Region subtract(Region other) {
        TreeSet<Zone> newZones = new TreeSet<Zone>(zones);
        newZones.removeAll(other.zones);
        return new Region(newZones);
    }

    /**
     * Extends this region with the zones from the other region. <p>This method
     * does not change the current region. It returns a new one.</p>
     *
     * @param other the other region to merge with this one.
     * @return the union of zones from this and the other regions.
     */
    public Region union(Region other) {
        TreeSet<Zone> newZones = new TreeSet<Zone>(zones);
        newZones.addAll(other.zones);
        return new Region(newZones);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Equality">
    /**
     * Two regions equal if they constitute of the same zones.
     *
     * @param obj the object with which to compare this region.
     * @return {@code true} if and only if {@code obj} is a region and it
     * contains the same zones.
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof Region) {
            return Sets.equal(zones, ((Region) obj).zones);
        }
        return false;
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = (zones == null || zones.isEmpty() ? 0 : zones.hashCode());
            hashInvalid = false;
        }
        return hash;
    }

    @Override
    public int compareTo(Region other) {
        if (other == null) {
            throw new NullPointerException();
        }
        return (this == other) ? 0 : Sets.compareNaturally(zones, other.zones);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    /**
     * Puts the string representation of this region into the provided string
     * builder.
     *
     * @param sb the string builder into which to write the string
     * representation of this region.
     * @throws IOException thrown if the string builder throws an exception. 
     */
    public void toString(Appendable sb) throws IOException {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        SpiderDiagram.printZoneList(sb, zones);
    }

    @Override
    public String toString() {
        try {
            StringBuilder sb = new StringBuilder();
            toString(sb);
            return sb.toString();
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }
    // </editor-fold>
}
