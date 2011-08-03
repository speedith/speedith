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

import java.util.Arrays;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.NavigableSet;
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
 * <p>You can construct new primary spider diagrams via the static methods in
 * {@link SpiderDiagrams}.</p>
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
    private TreeSet<String> spiders;
    private TreeMap<String, Region> habitats;
    private TreeSet<Zone> shadedZones;
    private boolean hashInvalid = true;
    private int hash;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates an empty primary (unitary) spider diagram.
     */
    PrimarySpiderDiagram() {
        spiders = null;
        habitats = null;
        shadedZones = null;
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
    PrimarySpiderDiagram(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
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
            if (!Sets.isNaturalSubset(habitats.navigableKeySet(), spiders)) {
                throw new IllegalArgumentException(i18n("ERR_SD_HABITATS_WITHOUT_SPIDERS"));
            }
        }
        // TODO: Check that no habitat is an empty or null region.
        this.spiders = spiders;
        this.habitats = habitats;
        this.shadedZones = shadedZones;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     * <p>Note: this method may return {@code null}.</p>
     * @return an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     */
    public SortedMap<String, Region> getHabitats() {
        return habitats == null ? null : Collections.unmodifiableSortedMap(habitats);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     */
    public int getHabitatsCount() {
        return habitats == null ? 0 : habitats.size();
    }

    /**
     * Returns an unmodifiable set of shaded {@link Zone zones} in this spider
     * diagram.
     * <p>Note: this method may return {@code null}.</p>
     * @return a set of shaded {@link Zone zones} in this spider diagram..
     */
    public SortedSet<Zone> getShadedZones() {
        return shadedZones == null ? null : Collections.unmodifiableSortedSet(shadedZones);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     */
    public int getShadedZonesCount() {
        return shadedZones == null ? 0 : shadedZones.size();
    }

    /**
     * Returns an unmodifiable set of spiders (their names) that appear in this
     * spider diagram.
     * <p>Note: this method may return {@code null}.</p>
     * @return a set of spiders (their names) that appear in this spider
     * diagram.
     */
    public SortedSet<String> getSpiders() {
        return spiders == null ? null : Collections.unmodifiableSortedSet(spiders);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     * @return the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     */
    public int getSpidersCount() {
        return spiders == null ? 0 : spiders.size();
    }

    /**
     * Returns the habitat of the given spider.
     * @param spider the name of the spider for which to return the habitat.
     * @return the habitat of the given spider.
     */
    public Region getSpiderHabitat(String spider) {
        return habitats == null ? null : habitats.get(spider);
    }

    /**
     * Checks whether the spider with the given name is present in this primary
     * spider diagram.
     * @param spider the name of the spider to check whether it is present in
     * this primary spider diagram.
     * @return {@code true} if and only if the spider is present in this primary
     * spider diagram.
     */
    public boolean containsSpider(String spider) {
        return spiders == null ? false : spiders.contains(spider);
    }

    /**
     * Returns a set of all contours that are mentioned in this primary spider
     * diagram.
     * <p>Note: this method never returns {@code null}. If there are no contours
     * then this method will return an empty set.</p>
     * @return a set of all contours that are mentioned in this primary spider
     * diagram.
     */
    public NavigableSet<String> getContours() {
        TreeSet<String> contours = new TreeSet<String>();
        if (habitats != null) {
            for (Region region : this.habitats.values()) {
                if (region.getZonesCount() > 0) {
                    for (Zone zone : region.getZones()) {
                        if (zone.getInContoursCount() > 0) {
                            contours.addAll(zone.getInContours());
                        }
                        if (zone.getOutContoursCount() > 0) {
                            contours.addAll(zone.getOutContours());
                        }
                    }
                }
            }
        }
        if (this.shadedZones != null) {
            for (Zone zone : this.shadedZones) {
                if (zone.getInContoursCount() > 0) {
                    contours.addAll(zone.getInContours());
                }
                if (zone.getOutContoursCount() > 0) {
                    contours.addAll(zone.getOutContours());
                }
            }
        }
        return contours;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="SpiderDiagram Implementation">
    @Override
    public SpiderDiagram transform(Transformer t, boolean trackParents) {
        if (t == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "t"));
        }
        SpiderDiagram curTransform = t.transform(this, 0, 0, null);
        return curTransform == null ? this : curTransform;
    }

    @Override
    public int getSubDiagramCount() {
        return 1;
    }

    @Override
    public SpiderDiagram getSubDiagramAt(int index) {
        if (index == 0) {
            return this;
        } else {
            throw new IndexOutOfBoundsException(i18n("GERR_INDEX_OUT_OF_BOUNDS"));
        }
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
    public boolean equalsSemantically(SpiderDiagram other) {
        if (equals(other)) {
            return true;
        }
        // Well, firstly, the diagrams have to be of the same type:
        if (other instanceof PrimarySpiderDiagram) {
            PrimarySpiderDiagram psd = (PrimarySpiderDiagram) other;
            // Let's say the primary spider diagrams have the same number of spiders:
            if (getSpidersCount() != psd.getSpidersCount()) {
                return false;
            }
            // Now they also have to have the same habitats (with possibly mixed
            // spider names)
            if (!__sameHabitats(psd)) {
                return false;
            }
            // Also, shaded zones should be the same!
            return equal(shadedZones, psd.shadedZones);
        }
        return false;
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = (spiders == null ? 0 : spiders.hashCode())
                    + (habitats == null ? 0 : habitats.hashCode())
                    + (shadedZones == null ? 0 : shadedZones.hashCode());
            hashInvalid = false;
        }
        return hash;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Transformation Methods">
    /**
     * Creates a new primary spider diagram that is a copy of this one, the only
     * difference being a different habitat for the chosen spider.
     * @param spider the spider for which to change the habitat.
     * @param newHabitat the new habitat of the spider.
     * @return a new primary spider diagram that is almost a copy of this one,
     * except the given spider will have the new habitat.
     */
    public PrimarySpiderDiagram changeSpiderHabitat(String spider, Region newHabitat) {
        if (spiders.contains(spider)) {
            TreeMap<String, Region> newHabitats = new TreeMap<String, Region>(this.habitats);
            newHabitats.put(spider, newHabitat);
            return SpiderDiagrams.createPrimarySD(this.spiders, newHabitats, shadedZones, false);
        } else {
            throw new IllegalArgumentException(i18n("ERR_SPIDER_NOT_IN_DIAGRAM", spider));
        }
    }
    //</editor-fold>

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
        if (habitats != null && !habitats.isEmpty()) {
            Iterator<Entry<String, Region>> spIterator = habitats.entrySet().iterator();
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
    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private boolean __isPsdEqual(PrimarySpiderDiagram psd) {
        return hashCode() == psd.hashCode()
                && equal(spiders, psd.spiders)
                && equal(habitats == null ? null : habitats.entrySet(), psd.habitats == null ? null : psd.habitats.entrySet())
                && equal(shadedZones, psd.shadedZones);
    }

    /**
     * Checks whether this and the given primary spider diagrams have the same
     * habitats for their spiders (invariant under spider names).
     * @param psd
     * @return 
     */
    private boolean __sameHabitats(PrimarySpiderDiagram psd) {
        if (getHabitatsCount() != psd.getHabitatsCount()) {
            return false;
        } else if (getHabitatsCount() <= 0) {
            return true;
        }
        // There are some habitats. We have to make sure that they are exactly
        // the same if both are sorted:
        Object[] habitatsA = habitats.values().toArray();
        Object[] habitatsB = psd.habitats.values().toArray();
        Arrays.sort(habitatsA);
        Arrays.sort(habitatsB);
        for (int i = 0; i < habitatsA.length; i++) {
            if (!habitatsA[i].equals(habitatsB[i])) {
                return false;
            }
        }
        return true;
    }
    // </editor-fold>
}
