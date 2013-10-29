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

import java.io.IOException;
import java.util.*;
import java.util.Map.Entry;
import propity.util.Sets;
import static propity.util.Sets.equal;
import static speedith.core.i18n.Translations.i18n;

/**
 * Represents a unitary spider diagram. For a complete and formal description of
 * spider diagrams see paper <a
 * href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924"
 * title="10.1112/S1461157000000942"> Spider Diagrams (2005)</a>. <p>It contains
 * all necessary information about the habitats of spiders, shaded zones,
 * contour names, zones etc.</p> <p>You can construct new primary spider
 * diagrams via the static methods in {@link SpiderDiagrams}.</p> <p>Instances
 * of this class (and its derived classes) are immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagram extends SpiderDiagram {

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The identifier of the primary (unitary) spider diagram in the textual
     * representation of spider diagrams. <p>This value is used in the textual
     * representation of spider diagrams (see
     * {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextPrimaryId = "PrimarySD";
    /**
     * The attribute key name for the list of habitats in the primary spider
     * diagram. <p>This value is used in the textual representation of spider
     * diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextHabitatsAttribute = "habitats";
    /**
     * The attribute key name for the list of shaded zones in the primary spider
     * diagram. <p>This value is used in the textual representation of spider
     * diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextShadedZonesAttribute = "sh_zones";
    /**
     * The attribute key name for the list of zones that are present in the
     * primary spider diagram (see
     * {@link PrimarySpiderDiagram#getPresentZones()}). <p>This value is used in
     * the textual representation of spider diagrams (see
     * {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextPresentZonesAttribute = "present_zones";
    /**
     * The attribute key name for the list of spiders in the primary spider
     * diagram. <p>This value is used in the textual representation of spider
     * diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextSpidersAttribute = "spiders";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private final TreeSet<String> spiders;
    private final TreeMap<String, Region> spiderHabitatsMap;
//    /**
//     * This array is used to quickly compare primary spider diagrams up to
//     * S-equivalence.
//     *
//     * <p>For example, for S-equivalence it is required (but not sufficient)
//     * that two spider diagrams have the same number of habitats and that all
//     * both lists of habitats, when sorted, are the same. </p>
//     */
//    private Region[] habitats;
    private final TreeSet<Zone> shadedZones;
    private TreeSet<String> contours;
    private final TreeSet<Zone> presentZones;
    private boolean hashInvalid = true;
    private int hash;
    private Boolean valid;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates an empty primary (unitary) spider diagram.
     */
    PrimarySpiderDiagram() {
        this(null, null, null, null);
    }

    /**
     * Creates an instance of a primary spider diagram with the given spiders,
     * their habitats and shaded zones. <p>This method makes copies of the given
     * parameters.</p>
     *
     * @param spiders a set of spiders (their names) that appear in this spider
     * diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}.
     * @param presentZones the set of zones that should be drawn in the diagram
     * if possible (see {@link PrimarySpiderDiagram#getPresentZones()}).
     */
    PrimarySpiderDiagram(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones, Collection<Zone> presentZones) {
        this(spiders == null ? null : new TreeSet<String>(spiders),
                habitats == null ? null : new TreeMap<String, Region>(habitats),
                shadedZones == null ? null : new TreeSet<Zone>(shadedZones),
                presentZones == null ? null : new TreeSet<Zone>(presentZones));
    }

    /**
     * Initialises a new primary spider diagram with the given set of spiders,
     * habitats and shaded zones. <p>Note that this method does <span
     * style="font-weight:bold">not</span> make copies of the input
     * parameters.</p>
     *
     * @param spiders a set of spiders (their names) that appear in this spider
     * diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}.
     * @param presentZones the set of zones that should be drawn in the diagram
     * if possible (see {@link PrimarySpiderDiagram#getPresentZones()}).
     */
    PrimarySpiderDiagram(TreeSet<String> spiders, TreeMap<String, Region> habitats, TreeSet<Zone> shadedZones, TreeSet<Zone> presentZones) {
        // TODO: This should be checked in 'isValid'. The construction of a
        // primary spider diagram should be as quick as possible (just reference
        // assignments). Also check that no habitat is an empty or null region
        // in the 'isValid' method.

        // Check that habitats don't talk about spiders not present in
        // 'spiders'.
        // If there aren't any spiders, then there should not be any habitats
        // too.
        if (spiders == null || spiders.isEmpty()) {
            if (habitats != null && !habitats.isEmpty()) {
                throw new IllegalArgumentException(i18n("ERR_SD_HABITATS_WITHOUT_SPIDERS"));
            }
        } else if (habitats != null) {
            // But if there are some spiders, then we have to check that the
            // habitats don't talk about non-existent spiders.
            if (!Sets.isNaturalSubset(habitats.navigableKeySet(), spiders)) {
                throw new IllegalArgumentException(i18n("ERR_SD_HABITATS_WITHOUT_SPIDERS"));
            }
        }

        this.spiders = spiders;
        this.spiderHabitatsMap = habitats;
        this.shadedZones = shadedZones;
        this.presentZones = presentZones;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}. <p>Note: this method may return
     * {@code null}.</p>
     *
     * @return an unmodifiable key-value map of spiders with their corresponding
     * {@link Region habitats}.
     */
    public SortedMap<String, Region> getHabitats() {
        return spiderHabitatsMap == null ? null : Collections.unmodifiableSortedMap(spiderHabitatsMap);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     *
     * @return the number of {@link PrimarySpiderDiagram#getHabitats() habitats}
     * specified in this primary spider diagram.
     */
    public int getHabitatsCount() {
        return spiderHabitatsMap == null ? 0 : spiderHabitatsMap.size();
    }

    /**
     * Returns an unmodifiable set of shaded {@link Zone zones} in this spider
     * diagram. <p>Note: this method may return {@code null}.</p>
     *
     * @return a set of shaded {@link Zone zones} in this spider diagram..
     */
    public SortedSet<Zone> getShadedZones() {
        return shadedZones == null ? null : Collections.unmodifiableSortedSet(shadedZones);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     *
     * @return the number of {@link PrimarySpiderDiagram#getShadedZones() shaded
     * zones} specified in this primary spider diagram.
     */
    public int getShadedZonesCount() {
        return shadedZones == null ? 0 : shadedZones.size();
    }

    /**
     * Returns a set of zones that should be drawn in the spider diagram. <p>It
     * should be noted that semantically equivalent spider diagrams can differ
     * in the way they are drawn. For example, a spider diagram showing two
     * disjoint sets A and B, can be drawn with the shaded intersection zone or
     * merely drawing the contours A and B spatially disconnected (without the
     * shaded intersection zone). This set indicates whether or not to draw such
     * zones.</p>
     *
     * @return a set of zones that should be drawn in the diagram. <p>May return
     * {@code null}.</p>
     */
    public SortedSet<Zone> getPresentZones() {
        return presentZones == null ? null : Collections.unmodifiableSortedSet(presentZones);
    }

    /**
     * Returns the number of zones in the <span
     * style="font-style:italic;">explicit present zones set</span>. <p>See
     * {@link PrimarySpiderDiagram#getPresentZones()} for a description on what
     * <span style="font-style:italic;">present zones</span> are.</p>
     *
     * @return the number of explicitly present zones.
     */
    public int getPresentZonesCount() {
        return presentZones == null ? 0 : presentZones.size();
    }

    /**
     * Returns an unmodifiable set of spiders (their names) that appear in this
     * spider diagram. <p>Note: this method may return {@code null}.</p>
     *
     * @return a set of spiders (their names) that appear in this spider
     * diagram.
     */
    public SortedSet<String> getSpiders() {
        return spiders == null ? null : Collections.unmodifiableSortedSet(spiders);
    }

    /**
     * Returns the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     *
     * @return the number of {@link PrimarySpiderDiagram#getSpiders() spiders}
     * specified in this primary spider diagram.
     */
    public int getSpidersCount() {
        return spiders == null ? 0 : spiders.size();
    }

    /**
     * Returns the habitat of the given spider.
     *
     * @param spider the name of the spider for which to return the habitat.
     * @return the habitat of the given spider.
     */
    public Region getSpiderHabitat(String spider) {
        return spiderHabitatsMap == null ? null : spiderHabitatsMap.get(spider);
    }

    /**
     * Checks whether the spider with the given name is present in this primary
     * spider diagram.
     *
     * @param spider the name of the spider to check whether it is present in
     * this primary spider diagram.
     * @return {@code true} if and only if the spider is present in this primary
     * spider diagram.
     */
    public boolean containsSpider(String spider) {
        return spiders == null ? false : spiders.contains(spider);
    }

    /**
     * <p>Returns a set of all contours that are mentioned in this primary
     * spider diagram.</p> <p><span style="font-weight:bold">Important</span>:
     * this method returns the set of all contours only if this primary spider
     * diagram is {@link
     * PrimarySpiderDiagram#isValid() valid}, otherwise an {@link UnsupportedOperationException
     * exception} is thrown.</p> <p>Note: this method never returns
     * {@code null}. If there are no contours then this method will return an
     * empty set.</p>
     *
     * @return an {@link Collections#unmodifiableSortedSet(java.util.SortedSet)
     * unmodifiable sorted set} of all contours that are mentioned in this
     * primary spider diagram.
     */
    public SortedSet<String> getAllContours() {
        if (isValid()) {
            return getContours();
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    /**
     * Returns the number of spider that have a foot in the given zone.
     * 
     * @param z
     * 
     * @return the number of spider that have a foot in the given zone.
     */
    public int getSpiderCountInZone(Zone z) {
        int count = 0;
        if (getHabitatsCount() > 0) {
            for (Region region : getHabitats().values()) {
                if (region.contains(z)) {
                    ++count;
                }
            }
        }
        return count;
    }
    
    /**
     * Returns the spiders that have a foot in the given zone.
     * 
     * @param z
     * 
     * @return the spiders that have a foot in the given zone.
     */
    public TreeSet<String> getSpidersInZone(Zone z) {
        TreeSet<String> count = new TreeSet<>();
        if (getHabitatsCount() > 0) {
            for (Entry<String, Region> habitat : getHabitats().entrySet()) {
                if (habitat.getValue().contains(z)) {
                    count.add(habitat.getKey());
                }
            }
        }
        return count;
    }

    @Override
    public boolean isValid() {
        if (valid == null) {
            valid = checkValid();
        }
        return valid;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="SpiderDiagram Implementation">
    @Override
    public SpiderDiagram transform(Transformer t, boolean trackParents) {
        if (t == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "t"));
        }
        SpiderDiagram curTransform = t.transform(this, 0, null, null);
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

    // <editor-fold defaultstate="collapsed" desc="Iterable Implementation">
    @Override
    public Iterator<SpiderDiagram> iterator() {
        return new AtomicSpiderDiagramIterator(this);
    }

    static class AtomicSpiderDiagramIterator implements Iterator<SpiderDiagram> {

        private SpiderDiagram sd;
        private boolean atStart = true;

        public AtomicSpiderDiagramIterator(SpiderDiagram sd) {
            if (sd == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sd"));
            }
            this.sd = sd;
        }

        @Override
        public boolean hasNext() {
            return atStart;
        }

        @Override
        public SpiderDiagram next() {
            if (atStart) {
                atStart = false;
                return sd;
            } else {
                throw new NoSuchElementException();
            }
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException(i18n("SD_ITER_REMOVE_NOT_SUPPORTED"));
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
    public boolean isSEquivalentTo(SpiderDiagram other) {
        if (equals(other)) {
            return true;
        }
        // Well, firstly, the diagrams have to be of the same type:
        if (other instanceof PrimarySpiderDiagram) {
            PrimarySpiderDiagram psd = (PrimarySpiderDiagram) other;
            // The primary spider diagrams must have the same number of spiders:
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

            // NOTE: Present zones do not influence the semantics of the spider
            // diagram.
        }
        return false;
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = (spiders == null ? 0 : spiders.hashCode())
                    + (spiderHabitatsMap == null ? 0 : spiderHabitatsMap.hashCode())
                    + (shadedZones == null ? 0 : shadedZones.hashCode())
                    + (presentZones == null ? 0 : presentZones.hashCode());
            hashInvalid = false;
        }
        return hash;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Transformation Methods">
    /**
     * Creates a copy of this primary spider diagram that contains the given
     * spider and its habitat. <p>If the original primary spider diagram already
     * contained this spider, then it is simply replaced.</p>
     *
     * @param spider the spider to be included in the new primary spider
     * diagram.
     * @param habitat the habitat of the spider.
     * @return a copy of this primary spider diagram that contains the given
     * spider and its habitat.
     */
    public PrimarySpiderDiagram addSpider(String spider, Region habitat) {
        // Add the habitat to the map of spiders and their habitats.
        TreeMap<String, Region> newHabitats = (spiderHabitatsMap == null) ? new TreeMap<String, Region>() : new TreeMap<String, Region>(spiderHabitatsMap);
        newHabitats.put(spider, habitat);
        // Now add the spider to the set of all spiders. Maybe we can reuse the 
        // set if it already contains the spider.
        TreeSet<String> newSpiders;
        if (spiders != null) {
            if (spiders.contains(spider)) {
                newSpiders = spiders;
            } else {
                newSpiders = new TreeSet<String>(spiders);
                newSpiders.add(spider);
            }
        } else {
            newSpiders = new TreeSet<String>();
            newSpiders.add(spider);
        }
        // Finally construct the spider diagram (without making any copies of
        // the spiders, habitats, and shaded zones collections).
        return SpiderDiagrams.createPrimarySD(newSpiders, newHabitats, shadedZones, presentZones, false);
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    @Override
    public void toString(Appendable sb) throws IOException {
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
        if (presentZones != null) {
            printPresentZones(sb.append(", "));
        }
        sb.append('}');
    }

    private void printSpiders(Appendable sb) {
        try {
            sb.append(SDTextSpidersAttribute).append(" = ");
            printStringList(sb, spiders);
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }

    private void printShadedZones(Appendable sb) {
        try {
            sb.append(SDTextShadedZonesAttribute).append(" = ");
            printZoneList(sb, shadedZones);
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }

    private void printPresentZones(Appendable sb) {
        try {
            sb.append(SDTextPresentZonesAttribute).append(" = ");
            printZoneList(sb, presentZones);
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }

    /**
     * Prints a list of habitats to the given {@link StringBuilder}. <p>The
     * output format is '{@code [ habitat, habitat, ... ]}'. See {@link
     * PrimarySpiderDiagram#printHabitat(java.lang.StringBuilder, java.lang.String, speedith.core.lang.Region)}
     * for a description of the habitat output format (for each habitat).</p>
     *
     * @param sb
     */
    private void printHabitats(Appendable sb) throws IOException {
        sb.append(SDTextHabitatsAttribute).append(" = ");
        sb.append('[');
        if (spiderHabitatsMap != null && !spiderHabitatsMap.isEmpty()) {
            Iterator<Entry<String, Region>> spIterator = spiderHabitatsMap.entrySet().iterator();
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
     * Outputs a single habitat into the {@link StringBuilder}. <p>The format of
     * the habitat is '{@code (spider, region)}' (it is a simple pair
     * tuple).</p>
     *
     * @param sb
     * @param spider
     * @param region
     */
    private static void printHabitat(Appendable sb, String spider, Region region) throws IOException {
        sb.append('(');
        printString(sb, spider);
        sb.append(", ");
        region.toString(sb);
        sb.append(')');
    }

    @Override
    public String toString() {
        try {
            final StringBuilder sb = new StringBuilder();
            toString(sb);
            return sb.toString();
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Equality Comparison Methods">
    /**
     * Checks for syntactical and
     *
     * @param psd
     * @return
     */
    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private boolean __isPsdEqual(PrimarySpiderDiagram psd) {
        return hashCode() == psd.hashCode()
                && equal(spiders, psd.spiders)
                && equal(spiderHabitatsMap == null ? null : spiderHabitatsMap.entrySet(), psd.spiderHabitatsMap == null ? null : psd.spiderHabitatsMap.entrySet())
                && equal(shadedZones, psd.shadedZones)
                && equal(presentZones, psd.presentZones);
    }

    /**
     * Checks whether this and the given primary spider diagrams have the same
     * habitats for their spiders (invariant under spider names). <p>This method
     * can be used to check for semantic equivalence.</p>
     *
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
        Object[] habitatsA = spiderHabitatsMap.values().toArray();
        Object[] habitatsB = psd.spiderHabitatsMap.values().toArray();
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

    // <editor-fold defaultstate="collapsed" desc="Contour Names Extraction">
    /**
     * Traverses all zones mentioned in this primary spider diagram and collects
     * all names of contours mentioned in these zones.
     */
    private void extractContours() {
        if (contours == null) {
            contours = new TreeSet<String>();
            if (extractContoursFromHabitats()
                    || extractContoursFromShadedZones()
                    || extractContoursFromPresentZones());
        }
    }

    private boolean extractContoursFromHabitats() {
        if (getHabitatsCount() > 0) {
            Region region = spiderHabitatsMap.firstEntry().getValue();
            if (region.getZonesCount() > 0) {
                Zone zone = region.getZones().first();
                if (zone.getInContoursCount() > 0) {
                    contours.addAll(zone.getInContours());
                }
                if (zone.getOutContoursCount() > 0) {
                    contours.addAll(zone.getOutContours());
                }
                return true;
            }
        }
        return false;
    }

    private boolean extractContoursFromShadedZones() {
        if (getShadedZonesCount() > 0) {
            Zone zone = shadedZones.first();
            if (zone.getInContoursCount() > 0) {
                contours.addAll(zone.getInContours());
            }
            if (zone.getOutContoursCount() > 0) {
                contours.addAll(zone.getOutContours());
            }
            return true;
        }
        return false;
    }

    private boolean extractContoursFromPresentZones() {
        if (this.presentZones != null) {
            Zone zone = presentZones.first();
            if (zone.getInContoursCount() > 0) {
                contours.addAll(zone.getInContours());
            }
            if (zone.getOutContoursCount() > 0) {
                contours.addAll(zone.getOutContours());
            }
            return true;
        }
        return false;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Validity Check Methods">
    /**
     * Checks whether this primary spider diagram is valid according to the
     * rules described in {@link PrimarySpiderDiagram#isValid()}.
     *
     * @return see {@link PrimarySpiderDiagram#isValid()}.
     */
    private boolean checkValid() {
        SortedSet<String> contours = getContours();
        if (areHabitatZonesValid(contours)
                && areShadedZonesValid(contours)
                && arePresentZonesValid(contours)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean arePresentZonesValid(SortedSet<String> contours) {
        if (this.presentZones != null) {
            for (Zone zone : presentZones) {
                if (!zone.isValid(contours)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean areShadedZonesValid(SortedSet<String> contours) {
        if (this.shadedZones != null) {
            for (Zone zone : this.shadedZones) {
                if (!zone.isValid(contours)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean areHabitatZonesValid(SortedSet<String> contours) {
        if (spiderHabitatsMap != null) {
            for (Region region : this.spiderHabitatsMap.values()) {
                if (region.getZonesCount() > 0) {
                    for (Zone zone : region.getZones()) {
                        if (!zone.isValid(contours)) {
                            return false;
                        }
                    }
                } else {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * <p><span style="font-weight:bold">Important</span>: this method returns
     * the set of all contours only if this primary spider diagram is {@link
     * PrimarySpiderDiagram#isValid() valid}.</p>
     *
     * <p>Returns a set of contours that are mentioned in a randomly chosen zone
     * of this primary spider diagram.</p>
     *
     * <p><span style="font-weight:bold">Q: </span>Why a <span
     * style="font-style:italic;">randomly chosen</span> zone?</p>
     *
     * <p><span style="font-weight:bold">A: </span>Because in a valid diagram
     * the unions of in- and out-contour sets of all zones are the same.</p>
     *
     * <p>Note: this method never returns {@code null}. If there are no contours
     * then this method will return an empty set.</p>
     *
     * @return an {@link Collections#unmodifiableSortedSet(java.util.SortedSet)
     * unmodifiable sorted set} of contours that are mentioned in a randomly
     * chosen zone of this primary spider diagram.
     */
    SortedSet<String> getContours() {
        extractContours();
        return Collections.unmodifiableSortedSet(contours);
    }
    // </editor-fold>
}
