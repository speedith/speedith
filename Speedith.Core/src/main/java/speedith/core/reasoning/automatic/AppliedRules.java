package speedith.core.reasoning.automatic;

import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Created by sl542 on 17/11/15.
 */
public class AppliedRules {

    private Map<SpiderDiagramWrapper, Set<String>> introContours;

    private Map<SpiderDiagramWrapper, Set<String>> removeContours;

    private Map<SpiderDiagramWrapper, Set<String>> copiedContours;

    private Map<SpiderDiagramWrapper, Set<Zone>> removedShading;


    public AppliedRules() {
        introContours = new HashMap<SpiderDiagramWrapper,Set<String>>();
        removeContours = new HashMap<SpiderDiagramWrapper,Set<String>>();
        removedShading = new HashMap<SpiderDiagramWrapper, Set<Zone>>();
        copiedContours = new HashMap<SpiderDiagramWrapper, Set<String>>();
    }

    /**
     * Adds a contour to the set of already introduced contours for
     * the given primary spider diagram
     * @param psd the Primary Spider diagram for which the contour shall be saved
     *            as already introduced
     * @param c the name of the contour
     */
    public void addIntroContour(SpiderDiagramWrapper psd, String c) {
        if (!introContours.containsKey(psd)) {
            introContours.put(psd, new HashSet<String>());
        }
        introContours.get(psd).add(c);
    }

    /**
     * Adds a contour to the set of already removed contours for
     * the given primary spider diagram
     * @param psd the Primary Spider diagram for which the contour shall be saved
     *            as already removed
     * @param c the name of the contour
     */
    public void addRemoveContour(SpiderDiagramWrapper psd, String c) {
        if (!removeContours.containsKey(psd)) {
            removeContours.put(psd, new HashSet<String>());
        }
        removeContours.get(psd).add(c);
    }

    public void addRemovedShading(SpiderDiagramWrapper sd, Zone z) {
        if (!removedShading.containsKey(sd)) {
            removedShading.put(sd, new HashSet<Zone>());
        }
        removedShading.get(sd).add(z);
    }

    public Set<String> getIntroducedContours(SpiderDiagramWrapper psd) {
        if (!introContours.containsKey(psd)) {
            introContours.put(psd, new HashSet<String>());
        }
        return introContours.get(psd);
    }

    public Set<String> getRemovedContours(SpiderDiagramWrapper psd) {
        if (!removeContours.containsKey(psd)) {
            removeContours.put(psd, new HashSet<String>());
        }
        return removeContours.get(psd);
    }

    public Set<Zone> getRemovedShading(SpiderDiagramWrapper sd) {
        if (!removedShading.containsKey(sd)) {
            removedShading.put(sd, new HashSet<Zone>());
        }
        return removedShading.get(sd);

    }

    public Set<String> getCopiedContours(SpiderDiagramWrapper psd) {
        if (!copiedContours.containsKey(psd)) {
            copiedContours.put(psd, new HashSet<String>());
        }
        return copiedContours.get(psd);
    }

    public void addCopiedContour(SpiderDiagramWrapper psd, String c) {
        if (!copiedContours.containsKey(psd)) {
            copiedContours.put(psd, new HashSet<String>());
        }
        copiedContours.get(psd).add(c);
    }

}
