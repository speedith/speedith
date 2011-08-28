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
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;

/**
 * This is a utility class providing the functionality to visualise {@link
 * SpiderDiagram spider diagrams} with the <span style="font-style:italic;">iCircles</span>
 * library.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class DiagramVisualisation {

    private static void drawPSD(PrimarySpiderDiagram psd1) throws HeadlessException, CannotDrawException {
        AbstractDescription ad = getAbstractDescription(psd1);
        drawAD(ad);
    }

    private static void drawAD(AbstractDescription ad) throws CannotDrawException, HeadlessException {
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, 300);

        CirclesPanel cp = new CirclesPanel("a sample CirclesPanel", "No failure message", cd, 300, true);

        JFrame viewingFrame = new JFrame("frame to hold a CirclesPanel");
        viewingFrame.getContentPane().add(cp);
        viewingFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        viewingFrame.pack();
        viewingFrame.setVisible(true);
    }

    private static void markZone(byte[] allZones, String[] allContours, Zone zone, byte code) {
        int inMask = getZoneInMask(allContours, zone);
        int outMask = ~getZoneOutMask(allContours, zone);
        for (int i = 0; i < allZones.length; i++) {
            if ((i & inMask) == inMask && (i | outMask) == outMask) {
                allZones[i] |= code;
            }
        }
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

    private static int getZoneOutMask(String[] allContours, Zone zone) {
        int mask = 0;
        if (zone.getOutContoursCount() > 0) {
            for (String outContour : zone.getOutContours()) {
                int contourIndex = Arrays.binarySearch(allContours, outContour);
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

    private static void addFeetForZone(TreeSet<AbstractBasicRegion> feet, TreeSet<AbstractBasicRegion> allVisibleZones, String[] allContours, HashMap<String, AbstractCurve> contourMap, Zone foot) {
        int inMask = getZoneInMask(allContours, foot);
        int outMask = ~getZoneOutMask(allContours, foot);
        int allZonesCount = 1 << allContours.length;
        for (int i = 0; i < allZonesCount; i++) {
            if ((i & inMask) == inMask && (i | outMask) == outMask) {
                AbstractBasicRegion abr = constructABR(allContours, i, contourMap);
                feet.add(abr);
            }
        }
    }

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private DiagramVisualisation() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    static AbstractDescription getAbstractDescription(PrimarySpiderDiagram psd) {
        // Look at AbstractDescription.makeForTesting for details on how to
        // build an AbstractDescription.

        TreeSet<String> contourStrings = psd.getContours();

        if (contourStrings.size() > 10) {
            throw new RuntimeException("Too many different contours. Unpractical for drawing.");
        }

        HashMap<String, AbstractCurve> contourMap = new HashMap<String, AbstractCurve>();
        TreeSet<AbstractCurve> contours = new TreeSet<AbstractCurve>();
//        TreeSet<AbstractBasicRegion> nonShadedZones = new TreeSet<AbstractBasicRegion>();
        TreeSet<AbstractBasicRegion> shadedHabitatZones = new TreeSet<AbstractBasicRegion>();
        TreeSet<AbstractBasicRegion> allVisibleZones = new TreeSet<AbstractBasicRegion>();

        String[] allContours = contourStrings.toArray(new String[contourStrings.size()]);

        // Now construct a list of all possible contours that are not shaded.
        int allZonesCount = 1 << contourStrings.size();
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

        // TODO: Add spiders.
        if (psd.getHabitatsCount() > 0) {
            SortedMap<String, Region> habitats = psd.getHabitats();
            for (Entry<String, Region> habitat : habitats.entrySet()) {
                TreeSet<AbstractBasicRegion> feet = new TreeSet<AbstractBasicRegion>();
                for (Zone foot : habitat.getValue().getZones()) {
                    // A Speedith's zone can correspond to many zones. Hence we
                    // should add all the necessary feet:
                    addFeetForZone(feet, allVisibleZones, allContours, contourMap, foot);
                }
                ad.addSpider(new AbstractSpider(feet, habitat.getKey()));
            }
        }

        return ad;
    }

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
        
//        AbstractDescription ad = AbstractDescription.makeForTesting("a b ab, ,a b", false);
        AbstractDescription ad = AbstractDescription.makeForTesting("A B C AB AC BC ABC, B,A AB ABC, B, B", false);
        Iterator<AbstractSpider> it = ad.getSpiderIterator();
        it.next().setName("s1");
        it.next().setName("s2");
        it.next().setName("s3");
        drawAD(ad);

        for (PrimarySpiderDiagram psd : psds) {
//            drawPSD(psd);
        }
    }
}
