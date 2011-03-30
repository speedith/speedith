/*
 *   Project: Speedith.Core
 * 
 * File name: PrimarySpiderDiagram.java
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
import java.util.HashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * Represents a unitary spider diagram.
 * <p>It contains all necessary information about the habitats of spiders,
 * shaded zones, contour names, zones etc.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagram extends SpiderDiagram {
    // TODO: Provide sets for spider names and shaded zones.
    // TODO: Provide a hash table of spiders with their corresponding habitats.
    // TODO: Provide a way to easily extract names of contours (perhaps maintain
    // a set of contour names, which is filled when it is first accessed).

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private SortedSet<String> spiders;
    private Map<String, Region> habitats;
    private SortedSet<Zone> shadedZones;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates an empty primary (unitary) spider diagram.
     */
    public PrimarySpiderDiagram() {
        spiders = new TreeSet<String>();
        habitats = new HashMap<String, Region>();
        shadedZones = new TreeSet<Zone>();
    }

    public PrimarySpiderDiagram(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
        this.spiders = spiders == null ? null : new TreeSet<String>(spiders);
        this.habitats = habitats == null ? null : new HashMap<String, Region>(habitats);
        this.shadedZones = shadedZones == null ? null : new TreeSet<Zone>(shadedZones);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    public Map<String, Region> getHabitats() {
        return habitats == null ? null : Collections.unmodifiableMap(habitats);
    }

    public SortedSet<Zone> getShadedZones() {
        return shadedZones == null ? null : Collections.unmodifiableSortedSet(shadedZones);
    }

    public SortedSet<String> getSpiders() {
        return spiders == null ? null : Collections.unmodifiableSortedSet(spiders);
    }
    // </editor-fold>
}
