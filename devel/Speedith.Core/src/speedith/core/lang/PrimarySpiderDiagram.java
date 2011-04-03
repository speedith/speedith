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

import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import static speedith.core.i18n.Translations.i18n;

/**
 * Represents a unitary spider diagram. For a complete and formal description of
 * spider diagrams see paper
 * <a href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924" title="10.1112/S1461157000000942">
 * Spider Diagrams (2005)</a>.
 * <p>It contains all necessary information about the habitats of spiders,
 * shaded zones, contour names, zones etc.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagram extends SpiderDiagram {
    // TODO: Provide a way to easily extract names of contours (perhaps maintain
    // a set of contour names, which is filled when it is first accessed).

    // <editor-fold defaultstate="collapsed" desc="Constants">
    public static final String SDTextPrimaryId = "PrimarySD";
    public static final String SDTextHabitatsAttribute = "habitats";
    public static final String SDTextShadedZonesAttribute = "sh_zones";
    public static final String SDTextSpidersAttribute = "spiders";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private SortedSet<String> spiders;
    private TreeMap<String, Region> habitats;
    private SortedSet<Zone> shadedZones;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates an empty primary (unitary) spider diagram.
     */
    public PrimarySpiderDiagram() {
        spiders = null;
        habitats = null;
        shadedZones = null;
    }

    /**
     * Creates an instance of a primary spider diagram with the given spiders,
     * their habitats and shaded zones.
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}.
     */
    public PrimarySpiderDiagram(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
        this.spiders = spiders == null ? null : new TreeSet<String>(spiders);
        this.habitats = habitats == null ? null : new TreeMap<String, Region>(habitats);
        this.shadedZones = shadedZones == null ? null : new TreeSet<Zone>(shadedZones);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     * @return an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     */
    public SortedMap<String, Region> getHabitats() {
        return habitats == null ? null : Collections.unmodifiableSortedMap(habitats);
    }

    /**
     * Returns a set of shaded {@link Zone zones} in this spider diagram.
     * @return a set of shaded {@link Zone zones} in this spider diagram..
     */
    public SortedSet<Zone> getShadedZones() {
        return shadedZones == null ? null : Collections.unmodifiableSortedSet(shadedZones);
    }

    /**
     * Returns a set of spiders (their names) that appear in this spider
     * diagram.
     * @return a set of spiders (their names) that appear in this spider
     * diagram.
     */
    public SortedSet<String> getSpiders() {
        return spiders == null ? null : Collections.unmodifiableSortedSet(spiders);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    @Override
    public void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        sb.append(SDTextPrimaryId);
        sb.append(" {");
        printSpiders(sb);
        sb.append(", ");
        printHabitats(sb);
        sb.append(", ");
        printShadedZones(sb);
        sb.append('}');
    }

    private void printSpiders(StringBuilder sb) {
        sb.append(SDTextSpidersAttribute).append(" = ");
        printStringList(sb, spiders);
    }

    private void printShadedZones(StringBuilder sb) {
        sb.append(SDTextShadedZonesAttribute).append(" = ");
        printZoneList(sb, shadedZones);
    }

    private void printHabitats(StringBuilder sb) {
        sb.append(SDTextHabitatsAttribute).append(" = ");
        sb.append('[');
        Iterator<Entry<String, Region>> spIterator = habitats.entrySet().iterator();
        if (spIterator.hasNext()) {
            Entry<String, Region> habitat = spIterator.next();
            printHabitat(sb, habitat.getKey(), habitat.getValue());
            while (spIterator.hasNext()) {
                habitat = spIterator.next();
                printHabitat(sb.append(", "), habitat.getKey(), habitat.getValue());
            }
        }
        sb.append(']');
    }

    private void printHabitat(StringBuilder sb, String key, Region value) {
        sb.append('(');
        printString(sb, key);
        sb.append(", ");
        value.toString(sb);
        sb.append(')');
    }
    // </editor-fold>
}
