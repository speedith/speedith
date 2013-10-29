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
package speedith.ui;

import icircles.abstractDescription.*;
import icircles.concreteDiagram.ConcreteDiagram;
import icircles.util.CannotDrawException;
import java.util.Map.Entry;
import java.util.*;
import javax.swing.JPanel;
import speedith.core.lang.*;
import static speedith.i18n.Translations.i18n;

/**
 * This is a utility class providing the functionality to visualise {@link
 * SpiderDiagram spider diagrams} with the <span style="font-style:italic;">iCircles</span>
 * library.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class DiagramVisualisation {
    
    //<editor-fold defaultstate="collapsed" desc="Constants">
    private static final int DefaultDiagramSize = 500;
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private DiagramVisualisation() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Creates an {@link AbstractDescription abstract description} from the given
     * {@link PrimarySpiderDiagram primary spider diagram}. This abstract description
     * can be used with the {@link DiagramVisualisation#getSpiderDiagramPanel(icircles.abstractDescription.AbstractDescription, int)}
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
        SortedSet<String> contourStrings = psd.getAllContours();

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
            final AbstractCurve abstractCurve = new AbstractCurve(contour);
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

    /**
     * Creates a {@link ConcreteDiagram concrete diagram} from the given {@link 
     * PrimarySpiderDiagram primary spider diagram}.
     * @param diagram the primary spider diagram from which to create its concrete
     * representation.
     * @return the concrete representation of the given primary spider diagram.
     * @throws CannotDrawException this exception is thrown if the concrete
     * spider diagram could not have been created for whatever reason.
     */
    public static ConcreteDiagram getConcreteDiagram(PrimarySpiderDiagram diagram) throws CannotDrawException {
        return ConcreteDiagram.makeConcreteDiagram(getAbstractDescription(diagram), DefaultDiagramSize);
    }

    /**
     * Creates a panel which is showing the given spider diagram.
     * @param sd the spider diagram to draw.
     * @return the panel which displays the given spider diagram.
     * @throws CannotDrawException this exception is thrown if the diagram cannot
     * be drawn for any reason.
     */
    public static JPanel getSpiderDiagramPanel(SpiderDiagram sd) throws CannotDrawException {
        return getSpiderDiagramPanel(sd, DefaultDiagramSize);
    }

    /**
     * Creates a panel which is showing the given primary spider diagram.
     * @param sd the primary spider diagram to draw.
     * @return the panel which displays the given primary spider diagram.
     * @throws CannotDrawException this exception is thrown if the diagram cannot
     * be drawn for any reason.
     */
    public static SpeedithCirclesPanel getSpiderDiagramPanel(PrimarySpiderDiagram sd) throws CannotDrawException {
        return getSpiderDiagramPanel(sd, DefaultDiagramSize);
    }

    /**
     * Creates a panel which is showing the given spider diagram.
     * @param sd the spider diagram to draw.
     * @param size the size of the diagram panel (the drawn spider diagram).
     * @return the panel which displays the given spider diagram.
     * @throws CannotDrawException this exception is thrown if the diagram cannot
     * be drawn for any reason.
     */
    public static JPanel getSpiderDiagramPanel(SpiderDiagram sd, int size) throws CannotDrawException {
        if (sd == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sd"));
        } else {
            if (sd instanceof PrimarySpiderDiagram) {
                return getSpiderDiagramPanel((PrimarySpiderDiagram) sd, size);
            } else if (sd instanceof CompoundSpiderDiagram) {
                return new SpiderDiagramPanel((CompoundSpiderDiagram) sd);
            } else if (sd instanceof NullSpiderDiagram) {
                return new NullSpiderDiagramPanel();
            } else {
                throw new AssertionError(i18n("GERR_ILLEGAL_STATE"));
            }
        }
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

    /**
     * TODO: Document.
     * @param ad
     * @param size
     * @return
     * @throws CannotDrawException
     */
    static SpeedithCirclesPanel getSpiderDiagramPanel(AbstractDescription ad, int size) throws CannotDrawException {
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, size);
        return new SpeedithCirclesPanel(cd);
    }

    /**
     * TODO: Document.
     * @param diagram
     * @param size
     * @return
     * @throws CannotDrawException
     */
    static SpeedithCirclesPanel getSpiderDiagramPanel(PrimarySpiderDiagram diagram, int size) throws CannotDrawException {
        final AbstractDescription ad = getAbstractDescription(diagram);
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, size);
        return new SpeedithCirclesPanel(cd);
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
