package speedith.core.reasoning.automatic;

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

    private Map<SpiderDiagramWrapper, Set<Zone>> removedShadedZones;

    private Map<SpiderDiagramWrapper, Set<Zone>> introducedShadedZones;

    private Map<SpiderDiagramWrapper, Set<Set<Zone>>> copiedShadings;


    public AppliedRules() {
        introContours = new HashMap<SpiderDiagramWrapper,Set<String>>();
        removeContours = new HashMap<SpiderDiagramWrapper,Set<String>>();
        removedShading = new HashMap<SpiderDiagramWrapper, Set<Zone>>();
        removedShadedZones= new HashMap<SpiderDiagramWrapper, Set<Zone>>();
        introducedShadedZones = new HashMap<SpiderDiagramWrapper, Set<Zone>>();
        copiedContours = new HashMap<SpiderDiagramWrapper, Set<String>>();
        copiedShadings = new HashMap<SpiderDiagramWrapper, Set<Set<Zone>>>();

    }

    public AppliedRules(AppliedRules old) {
        this.introContours = new HashMap<> ();
        for( SpiderDiagramWrapper key: old.introContours.keySet()) {
            this.introContours.put(key, new HashSet<String>(old.introContours.get(key)));
        }
        this.removeContours = new HashMap<>();
        for (SpiderDiagramWrapper key: old.removeContours.keySet()) {
            this.removeContours.put(key, new HashSet<String>(old.removeContours.get(key)));
        }
        this.copiedContours = new HashMap<>();
        for (SpiderDiagramWrapper key: old.copiedContours.keySet()) {
            this.copiedContours.put(key, new HashSet<String>(old.copiedContours.get(key)));
        }
        this.removedShading = new HashMap<>();
        for (SpiderDiagramWrapper key: old.removedShading.keySet()) {
            this.removedShading.put(key, new HashSet<Zone>(old.removedShading.get(key)));
        }
        this.removedShadedZones = new HashMap<>();
        for (SpiderDiagramWrapper key: old.removedShadedZones.keySet()) {
            this.removedShadedZones.put(key, new HashSet<Zone>(old.removedShadedZones.get(key)));
        }
        this.introducedShadedZones = new HashMap<>();
        for (SpiderDiagramWrapper key: old.introducedShadedZones.keySet()) {
            this.introducedShadedZones.put(key, new HashSet<Zone>(old.introducedShadedZones.get(key)));
        }
        this.copiedShadings = new HashMap<>();
        for (SpiderDiagramWrapper key: old.copiedShadings.keySet()) {
            this.copiedShadings.put(key, new HashSet<Set<Zone>>(old.copiedShadings.get(key)));
        }
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

    public void addRemovedShadedZones(SpiderDiagramWrapper sd, Zone z) {
        if (!removedShadedZones.containsKey(sd)) {
            removedShadedZones.put(sd, new HashSet<Zone>());
        }
        removedShadedZones.get(sd).add(z);
    }

    public void addIntroducedShadedZones(SpiderDiagramWrapper sd, Zone z) {
        if (!introducedShadedZones.containsKey(sd)) {
            introducedShadedZones.put(sd, new HashSet<Zone>());
        }
        introducedShadedZones.get(sd).add(z);
    }


    public void addCopiedShadings(SpiderDiagramWrapper sd, Set<Zone> z) {
        if (!copiedShadings.containsKey(sd)) {
            copiedShadings.put(sd, new HashSet<Set<Zone>>());
        }
        copiedShadings.get(sd).add(z);
    }

    public Set<Set<Zone>> getCopiedShadings(SpiderDiagramWrapper psd) {
        if (!copiedShadings.containsKey(psd)) {
            copiedShadings.put(psd, new HashSet<Set<Zone>>());
        }
        return copiedShadings.get(psd);
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

    public Set<Zone> getRemovedShadedZones(SpiderDiagramWrapper sd) {
        if (!removedShadedZones.containsKey(sd)) {
            removedShadedZones.put(sd, new HashSet<Zone>());
        }
        return removedShadedZones.get(sd);

    }

    public Set<Zone> getIntroducedShadedZones(SpiderDiagramWrapper sd) {
        if (!introducedShadedZones.containsKey(sd)) {
            introducedShadedZones.put(sd, new HashSet<Zone>());
        }
        return introducedShadedZones.get(sd);

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
