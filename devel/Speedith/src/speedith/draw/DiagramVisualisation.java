/*
 *   Project: Speedith
 *
 * File name: DiagramVisualisation.java
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
package speedith.draw;

import java.util.SortedSet;
import icircles.abstractDescription.AbstractBasicRegion;
import icircles.abstractDescription.AbstractCurve;
import icircles.abstractDescription.AbstractDescription;
import icircles.abstractDescription.AbstractSpider;
import icircles.abstractDescription.CurveLabel;
import icircles.concreteDiagram.ConcreteDiagram;
import icircles.gui.CirclesPanel;
import icircles.util.CannotDrawException;
import java.awt.HeadlessException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.TreeSet;
import javax.swing.JFrame;
import javax.swing.JPanel;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import static speedith.i18n.Translations.*;

/**
 * This is a utility class providing the functionality to visualise {@link
 * SpiderDiagram spider diagrams} with the <span style="font-style:italic;">iCircles</span>
 * library.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class DiagramVisualisation {

    // <editor-fold defaultstate="collapsed" desc="Deprecated Methods">
    @Deprecated
    private static void drawPSD(PrimarySpiderDiagram psd1) throws HeadlessException, CannotDrawException {
        AbstractDescription ad = getAbstractDescription(psd1);
        drawAD(ad);
    }

    @Deprecated
    private static void drawAD(AbstractDescription ad) throws CannotDrawException, HeadlessException {
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, 300);

        CirclesPanel cp = new CirclesPanel("", "No failure message", cd, 300, true);

        JFrame viewingFrame = new JFrame("");
        viewingFrame.getContentPane().add(cp);
        viewingFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        viewingFrame.pack();
        viewingFrame.setVisible(true);
    }

    @Deprecated
    public static void main(String[] args) throws ReadingException, CannotDrawException {

        ArrayList<PrimarySpiderDiagram> psds = new ArrayList<PrimarySpiderDiagram>();
        PrimarySpiderDiagram psd1;
        // This hangs.
        //        PrimarySpiderDiagram psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
        //        psds.add(psd1);
        // This is okay, because it is a Venn diagram. But the outside should not be shaded.
        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        // This is not okay. We do not know whether A and B are disjoint. Also,
        // the outside of A and B must not be shaded.
        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        // This is not what I want. A is not necessarily a subset of B and the outside must not be empty!
        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], []), ([\"A\"],[\"B\"])]), (\"s'\", [([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], []), ([\"A\"],[\"B\"])]), (\"s'\", [([\"A\", \"B\"], []), ([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [([\"A\", \"B\"], [])], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], []), ([\"A\"],[\"B\"])]), (\"s'\", [([\"A\", \"B\"], []), ([\"B\"], [\"A\"])])]}");
        psds.add(psd1);

        psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [([\"B\"], [\"A\", \"C\"])], spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], []), ([\"A\"],[\"B\",  \"C\"])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])]}");
        psds.add(psd1);

//        AbstractDescription ad = AbstractDescription.makeForTesting("a b ab, ,a b", false);
//        AbstractDescription ad = AbstractDescription.makeForTesting("A B C AB AC BC ABC, B,A AB ABC, B, B", false);
//        Iterator<AbstractSpider> it = ad.getSpiderIterator();
//        it.next().setName("s1");
//        it.next().setName("s2");
//        it.next().setName("s3");
//        drawAD(ad);

        for (PrimarySpiderDiagram psd : psds) {
            drawPSD(psd);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private DiagramVisualisation() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Creates an {@link AbstractDescription abstract description} from the given
     * {@link PrimarySpiderDiagram primary spider diagram}. This abstract description
     * can be used with the {@link DiagramVisualisation#getCirclesPanel(icircles.abstractDescription.AbstractDescription, int)}
     * method, which returns a {@link JPanel panel} that actually draws the given
     * diagram.
     * @param psd the primary spider diagram for which to create an abstract description.
     * @return an abstract description of the spider diagram that corresponds to
     * the given primary spider diagram.
     * @throws CannotDrawException This exception is thrown if there are too many
     * contours in the diagram.
     */
    public static AbstractDescription getAbstractDescription(PrimarySpiderDiagram psd) throws CannotDrawException {

        // Make sure that the primary spider diagram is valid:
        if (psd == null || !psd.isValid()) {
            throw new CannotDrawException(i18n("DRAW_NOT_VALID_PSD"));
        }

        // Now we fetch all the contours that are mentioned in a primary spider
        // diagram.
        SortedSet<String> contourStrings = psd.getContours();

        if (contourStrings.size() > 10) {
            throw new CannotDrawException(i18n("TOO_MANY_CONTOURS"));
        }

        HashMap<String, AbstractCurve> contourMap = new HashMap<String, AbstractCurve>();
        TreeSet<AbstractCurve> contours = new TreeSet<AbstractCurve>();
        TreeSet<AbstractBasicRegion> shadedHabitatZones = new TreeSet<AbstractBasicRegion>();
        TreeSet<AbstractBasicRegion> allVisibleZones = new TreeSet<AbstractBasicRegion>();

        String[] allContours = contourStrings.toArray(new String[contourStrings.size()]);

        // Now construct a list of all possible zones. There are 2^size(contours)
        // zones. This is why we don't want more than say 10 contours... Things
        // just blow up otherwise.
        int allZonesCount = 1 << contourStrings.size();
        // This array contains bit flags for each zone. The flags indicate whether
        // a particular zone is shaded or whether is part of a spider's habitat
        // (or both).
        byte[] allZones = new byte[allZonesCount];
        final byte IsShaded = 1;
        final byte IsInHabitat = 2;

        // Get all contours in any way mentioned in the primary spider diagram:
        for (String contour : contourStrings) {
            final AbstractCurve abstractCurve = new AbstractCurve(CurveLabel.get(contour));
            contourMap.put(contour, abstractCurve);
            contours.add(abstractCurve);
        }

        // Now also get all the zones specified in spiders' habitats:
        if (psd.getHabitatsCount() > 0) {
            for (Region region : psd.getHabitats().values()) {
                for (Zone zone : region.getZones()) {
                    // Mark this zone as being part of a spider's habitat.
                    markZone(allZones, allContours, zone, IsInHabitat);
                }
            }
        }

        // Finally, get the shaded zones:
        if (psd.getShadedZonesCount() > 0) {
            for (Zone zone : psd.getShadedZones()) {
                markZone(allZones, allContours, zone, IsShaded);
            }
        }

        // Now get all the zones that are not shaded:
        for (int i = 0; i < allZones.length; i++) {
            byte b = allZones[i];
            if ((b & IsShaded) == 0) {
                // The zone is not shaded. Put it into the list of non-shaded zones.
                final AbstractBasicRegion abr = constructABR(allContours, i, contourMap);
                allVisibleZones.add(abr);
            } else if ((b & IsInHabitat) != 0) {
                // The zone is shaded and it is also in a habitat of a spider.
                // This means that we have to specify it as a shaded zone (to
                // force it being drawn).
                final AbstractBasicRegion abr = constructABR(allContours, i, contourMap);
                allVisibleZones.add(abr);
                shadedHabitatZones.add(abr);
            }
        }
        AbstractDescription ad = new AbstractDescription(contours, allVisibleZones, shadedHabitatZones);

        if (psd.getHabitatsCount() > 0) {
            SortedMap<String, Region> habitats = psd.getHabitats();
            for (Entry<String, Region> habitat : habitats.entrySet()) {
                TreeSet<AbstractBasicRegion> feet = new TreeSet<AbstractBasicRegion>();
                for (Zone foot : habitat.getValue().getZones()) {
                    // A Speedith's zone can correspond to many zones. Hence we
                    // should add all the necessary feet:
                    addFeetForZone(feet, contourMap, foot);
                }
                ad.addSpider(new AbstractSpider(feet, habitat.getKey()));
            }
        }

        return ad;
    }

    public static CirclesPanel getCirclesPanel(AbstractDescription ad, int size) throws CannotDrawException {
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, size);
        return new CirclesPanel("", "No failure message", cd, size, true);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    /**
     * This method assigns the given code to the given zone in the 'allZones'
     * array.
     * <p>This method effectively flags the zone with the given code.</p>
     */
    private static void markZone(byte[] allZones, String[] allContours, Zone zone, byte code) {
        // We have to mark the zone with the given code. But how do we determine
        // the index of the zone?
        // Well, say we have N contours. Then a zone is specified with N bits,
        // where 1 means that the zone is inside that contour and 0 means that
        // the zone is outside.
        // The resulting number is the index of the zone.
        allZones[getZoneInMask(allContours, zone)] |= code;
    }

    private static int getZoneInMask(String[] allContours, Zone zone) {
        int mask = 0;
        if (zone.getInContoursCount() > 0) {
            for (String inContour : zone.getInContours()) {
                int contourIndex = Arrays.binarySearch(allContours, inContour);
                mask |= (1 << contourIndex);
            }
        }
        return mask;
    }

    private static AbstractBasicRegion constructABR(String[] allContours, int zoneIndex, HashMap<String, AbstractCurve> contourMap) {
        TreeSet<AbstractCurve> inContours = new TreeSet<AbstractCurve>();
        for (int i = 0; i < allContours.length; i++) {
            if ((zoneIndex & (1 << i)) != 0) {
                inContours.add(contourMap.get(allContours[i]));
            }
        }
        return AbstractBasicRegion.get(inContours);
    }

    private static AbstractBasicRegion constructABR(Zone foot, HashMap<String, AbstractCurve> contourMap) {
        TreeSet<AbstractCurve> inContours = new TreeSet<AbstractCurve>();
        if (foot.getInContoursCount() > 0) {
            for (String inContour : foot.getInContours()) {
                inContours.add(contourMap.get(inContour));
            }
        }
        return AbstractBasicRegion.get(inContours);
    }

    private static void addFeetForZone(TreeSet<AbstractBasicRegion> feet, HashMap<String, AbstractCurve> contourMap, Zone foot) {
        feet.add(constructABR(foot, contourMap));
    }
    // </editor-fold>
}
