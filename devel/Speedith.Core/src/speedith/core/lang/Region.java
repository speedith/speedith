/*
 *   Project: Speedith.Core
 * 
 * File name: Region.java
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
package speedith.core.lang;

import java.util.Collection;
import java.util.Collections;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * This class represents a region in spider diagrams.
 * <p>A region is a union of zones. Thus the {@link Region} class contains 
 * {@link Region#getZones() a set of zones} which constitute it.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Region {

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private TreeSet<Zone> zones;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new region from the given collection of zones. The resulting
     * region will constitute of these zones.
     * <p>Note that duplicate zones in the given collection will be ignored.</p>
     * @param zones the collection of zones from which to construct this region.
     * <p>This argument may be {@code null}. This indicates an empty region.</p>
     */
    public Region(Collection<Zone> zones) {
        if (zones == null) {
            this.zones = null;
        } else {
            this.zones = new TreeSet<Zone>(zones);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns a set of {@link Zone zones} which make up this region.
     * <p>Note: this method may return {@code null}, which indicates an empty
     * region.</p>
     * @return a set of {@link Zone zones} which make up this region.
     * <p>Note: this method may return {@code null}, which indicates an empty
     * region.</p>
     */
    public SortedSet<Zone> getZones() {
        return zones == null ? null : Collections.unmodifiableSortedSet(zones);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Two regions equal if they constitute of the same zones.
     * @param obj the object with which to compare this region.
     * @return {@code true} if and only if {@code obj} is a region and it
     * contains the same zones.
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof Region) {
            Region r = (Region) obj;
            if (zones == null) {
                return r.zones == null || r.zones.isEmpty();
            } else if (r.zones == null) {
                return zones.isEmpty();
            } else {
                return zones.equals(r.zones);
            }
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 37 * hash + (this.zones != null ? this.zones.hashCode() : 0);
        return hash;
    }
    // </editor-fold>
}
