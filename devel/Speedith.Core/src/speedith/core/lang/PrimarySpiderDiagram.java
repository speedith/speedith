/*
 *   Project: Speedith.Core
 * 
 * File name: PrimarySpiderDiagram.java
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

import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import speedith.core.util.Sets;
import static speedith.core.i18n.Translations.i18n;
import static speedith.core.util.Sets.equal;

/**
 * Represents a unitary spider diagram. For a complete and formal description of
 * spider diagrams see paper
 * <a href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924" title="10.1112/S1461157000000942">
 * Spider Diagrams (2005)</a>.
 * <p>It contains all necessary information about the habitats of spiders,
 * shaded zones, contour names, zones etc.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagram extends SpiderDiagram {
    // TODO: Provide a way to easily extract names of contours (perhaps maintain
    // a set of contour names, which is filled when it is first accessed).

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The identifier of the primary (unitary) spider diagram in the textual representation
     * of spider diagrams.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextPrimaryId = "PrimarySD";
    /**
     * The attribute key name for the list of habitats in the primary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextHabitatsAttribute = "habitats";
    /**
     * The attribute key name for the list of shaded zones in the primary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextShadedZonesAttribute = "sh_zones";
    /**
     * The attribute key name for the list of spiders in the primary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextSpidersAttribute = "spiders";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private TreeSet<String> m_spiders;
    private TreeMap<String, Region> m_habitats;
    private TreeSet<Zone> m_shadedZones;
    private boolean m_hashInvalid = true;
    private int m_hash;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates an empty primary (unitary) spider diagram.
     */
    public PrimarySpiderDiagram() {
        m_spiders = null;
        m_habitats = null;
        m_shadedZones = null;
    }

    /**
     * Creates an instance of a primary spider diagram with the given spiders,
     * their habitats and shaded zones.
     * <p>This method makes copies of the given parameters.</p>
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}.
     */
    public PrimarySpiderDiagram(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
        this(spiders == null ? null : new TreeSet<String>(spiders),
                habitats == null ? null : new TreeMap<String, Region>(habitats),
                shadedZones == null ? null : new TreeSet<Zone>(shadedZones));
    }

    /**
     * Initialises a new primary spider diagram with the given set of spiders,
     * habitats and shaded zones.
     * <p>Note that this method does <span style="font-weight:bold">not</span>
     * make copies of the input parameters.</p>
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}. 
     */
    PrimarySpiderDiagram(TreeSet<String> spiders, TreeMap<String, Region> habitats, TreeSet<Zone> shadedZones) {
        // Check that habitats don't talk about spiders not present in
        // 'spiders'.
        // If there aren't any spiders, then there should not be any habitats
        // too.
        if (spiders == null || spiders.size() < 1) {
            if (habitats != null && habitats.size() > 0) {
                throw new IllegalArgumentException(i18n("ERR_SD_HABITATS_WITHOUT_SPIDERS"));
            }
        } else if (habitats != null) {
            // But if there are some spiders, then we have to check that the
            // habitats don't talk about non-existent spiders.
            if (!Sets.isDifferenceEmptyN(habitats.navigableKeySet(), spiders)) {
                throw new IllegalArgumentException(i18n("ERR_SD_HABITATS_WITHOUT_SPIDERS"));
            }
        }
        this.m_spiders = spiders;
        this.m_habitats = habitats;
        this.m_shadedZones = shadedZones;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     * <p>Note: this method may return {@code null}.</p>
     * @return an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     */
    public SortedMap<String, Region> getHabitats() {
        return m_habitats == null ? null : Collections.unmodifiableSortedMap(m_habitats);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     */
    public int getHabitatsCount() {
        return m_habitats == null ? 0 : m_habitats.size();
    }

    /**
     * Returns an unmodifiable set of shaded {@link Zone zones} in this spider
     * diagram.
     * <p>Note: this method may return {@code null}.</p>
     * @return a set of shaded {@link Zone zones} in this spider diagram..
     */
    public SortedSet<Zone> getShadedZones() {
        return m_shadedZones == null ? null : Collections.unmodifiableSortedSet(m_shadedZones);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     */
    public int getShadedZonesCount() {
        return m_shadedZones == null ? 0 : m_shadedZones.size();
    }

    /**
     * Returns an unmodifiable set of spiders (their names) that appear in this
     * spider diagram.
     * <p>Note: this method may return {@code null}.</p>
     * @return a set of spiders (their names) that appear in this spider
     * diagram.
     */
    public SortedSet<String> getSpiders() {
        return m_spiders == null ? null : Collections.unmodifiableSortedSet(m_spiders);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     */
    public int getSpidersCount() {
        return m_spiders == null ? 0 : m_spiders.size();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Equality">
    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        } else if (other instanceof PrimarySpiderDiagram) {
            return __isPsdEqual((PrimarySpiderDiagram) other);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        if (m_hashInvalid) {
            m_hash = m_spiders.hashCode() + m_habitats.hashCode() + m_shadedZones.hashCode();
            m_hashInvalid = false;
        }
        return m_hash;
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
        printStringList(sb, m_spiders);
    }

    private void printShadedZones(StringBuilder sb) {
        sb.append(SDTextShadedZonesAttribute).append(" = ");
        printZoneList(sb, m_shadedZones);
    }

    /**
     * Prints a list of habitats to the given {@link StringBuilder}.
     * <p>The output format is '{@code [ habitat, habitat, ... ]}'. See {@link
     * PrimarySpiderDiagram#printHabitat(java.lang.StringBuilder, java.lang.String, speedith.core.lang.Region)}
     * for a description of the habitat output format (for each habitat).</p>
     * @param sb 
     */
    private void printHabitats(StringBuilder sb) {
        sb.append(SDTextHabitatsAttribute).append(" = ");
        sb.append('[');
        if (m_habitats != null && !m_habitats.isEmpty()) {
            Iterator<Entry<String, Region>> spIterator = m_habitats.entrySet().iterator();
            if (spIterator.hasNext()) {
                Entry<String, Region> habitat = spIterator.next();
                printHabitat(sb, habitat.getKey(), habitat.getValue());
                while (spIterator.hasNext()) {
                    habitat = spIterator.next();
                    printHabitat(sb.append(", "), habitat.getKey(), habitat.getValue());
                }
            }
        }
        sb.append(']');
    }

    /**
     * Outputs a single habitat into the {@link StringBuilder}.
     * <p>The format of the habitat is '{@code (spider, region)}' (it is a
     * simple pair tuple).</p>
     * @param sb
     * @param spider
     * @param region 
     */
    private static void printHabitat(StringBuilder sb, String spider, Region region) {
        sb.append('(');
        printString(sb, spider);
        sb.append(", ");
        region.toString(sb);
        sb.append(')');
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        toString(sb);
        return sb.toString();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    private boolean __isPsdEqual(PrimarySpiderDiagram psd) {
        return equal(this.m_spiders, psd.m_spiders)
                && equal(this.m_habitats.entrySet(), psd.m_habitats.entrySet())
                && equal(this.m_shadedZones, psd.m_shadedZones);
    }
    // </editor-fold>
}
