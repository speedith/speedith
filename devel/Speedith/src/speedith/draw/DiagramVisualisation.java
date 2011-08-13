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
import icircles.abstractDescription.CurveLabel;
import icircles.concreteDiagram.ConcreteDiagram;
import icircles.gui.CirclesPanel;
import icircles.util.CannotDrawException;
import java.util.HashMap;
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

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private DiagramVisualisation() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    static AbstractDescription getAbstractDescription(PrimarySpiderDiagram psd) {
        HashMap<String, AbstractCurve> contourMap = new HashMap<String, AbstractCurve>();
        TreeSet<AbstractCurve> contours = new TreeSet<AbstractCurve>();
        TreeSet<AbstractBasicRegion> zones = new TreeSet<AbstractBasicRegion>();
        TreeSet<AbstractBasicRegion> shZones = new TreeSet<AbstractBasicRegion>();
        // Get all contours in any way mentioned in the primary spider diagram:
        for (String contour : psd.getContours()) {
            final AbstractCurve abstractCurve = new AbstractCurve(CurveLabel.get(contour));
            contourMap.put(contour, abstractCurve);
            contours.add(abstractCurve);
        }
        // Now also get all the zones specified in spiders' habitats:
        if (psd.getHabitatsCount() > 0) {
            for (Region region : psd.getHabitats().values()) {
                for (Zone zone : region.getZones()) {
                    final TreeSet<AbstractCurve> inContours = new TreeSet<AbstractCurve>();
                    for (String inContour : zone.getInContours()) {
                        inContours.add(contourMap.get(inContour));
                    }
                    zones.add(AbstractBasicRegion.get(inContours));
                }
            }
        }
        // Finally, get the shaded zones:
        if (psd.getShadedZonesCount() > 0) {
            for (Zone zone : psd.getShadedZones()) {
                final TreeSet<AbstractCurve> inContours = new TreeSet<AbstractCurve>();
                for (String inContour : zone.getInContours()) {
                    inContours.add(contourMap.get(inContour));
                }
                shZones.add(AbstractBasicRegion.get(inContours));
            }
        }
        return new AbstractDescription(contours, zones, shZones);
    }

    public static void main(String[] args) throws ReadingException, CannotDrawException {
        // This hangs.
//        PrimarySpiderDiagram psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
        
        // This is okay, because it is a Venn diagram. But the outside should not be shaded.
        PrimarySpiderDiagram psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
           
        // This is not okay. We do not know whether A and B are disjoint. Also,                          
        // the outside of A and B must not be shaded.
//        PrimarySpiderDiagram psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}");
        
        // This is not what I want. A is not necessarily a subset of B and the outside must not be empty!
//        PrimarySpiderDiagram psd1 = (PrimarySpiderDiagram) SpiderDiagramsReader.readSpiderDiagram("PrimarySD { sh_zones = [], spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"B\"], [\"A\"])])]}");
        
        
        AbstractDescription ad = getAbstractDescription(psd1);
        ConcreteDiagram cd = ConcreteDiagram.makeConcreteDiagram(ad, 100);

        CirclesPanel cp = new CirclesPanel("a sample CirclesPanel", "No failure message", cd, 300, true);

        JFrame viewingFrame = new JFrame("frame to hold a CirclesPanel");
        viewingFrame.getContentPane().add(cp);
        viewingFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        viewingFrame.pack();
        viewingFrame.setVisible(true);
    }
    // </editor-fold>
}
