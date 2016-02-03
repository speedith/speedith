package speedith.core.reasoning.automatic;

import speedith.core.lang.Zone;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Created by sl542 on 17/11/15.
 */
public class AppliedRules {

    private Map<SpiderDiagramOccurrence, Set<String>> introContours;

    private Map<SpiderDiagramOccurrence, Set<String>> removeContours;

    private Map<SpiderDiagramOccurrence, Set<String>> copiedContours;

    private Map<SpiderDiagramOccurrence, Set<Zone>> removedShading;

//    private Map<SpiderDiagramOccurrence, Set<Zone>> removedShadedZones;

//    private Map<SpiderDiagramOccurrence, Set<Zone>> introducedShadedZones;

    private Map<SpiderDiagramOccurrence, Set<Set<Zone>>> copiedShadings;


    public AppliedRules() {
        introContours = new HashMap<SpiderDiagramOccurrence,Set<String>>();
        removeContours = new HashMap<SpiderDiagramOccurrence,Set<String>>();
        removedShading = new HashMap<SpiderDiagramOccurrence, Set<Zone>>();
//        removedShadedZones= new HashMap<SpiderDiagramOccurrence, Set<Zone>>();
//        introducedShadedZones = new HashMap<SpiderDiagramOccurrence, Set<Zone>>();
        copiedContours = new HashMap<SpiderDiagramOccurrence, Set<String>>();
        copiedShadings = new HashMap<SpiderDiagramOccurrence, Set<Set<Zone>>>();

    }

    public AppliedRules(AppliedRules old) {
        this.introContours = new HashMap<> ();
        for( SpiderDiagramOccurrence key: old.introContours.keySet()) {
            this.introContours.put(key, new HashSet<String>(old.introContours.get(key)));
        }
        this.removeContours = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.removeContours.keySet()) {
            this.removeContours.put(key, new HashSet<String>(old.removeContours.get(key)));
        }
        this.copiedContours = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.copiedContours.keySet()) {
            this.copiedContours.put(key, new HashSet<String>(old.copiedContours.get(key)));
        }
        this.removedShading = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.removedShading.keySet()) {
            this.removedShading.put(key, new HashSet<Zone>(old.removedShading.get(key)));
        }
/*        this.removedShadedZones = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.removedShadedZones.keySet()) {
            this.removedShadedZones.put(key, new HashSet<Zone>(old.removedShadedZones.get(key)));
        }

        this.introducedShadedZones = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.introducedShadedZones.keySet()) {
            this.introducedShadedZones.put(key, new HashSet<Zone>(old.introducedShadedZones.get(key)));
        }
        */
        this.copiedShadings = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.copiedShadings.keySet()) {
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
    public void addIntroContour(SpiderDiagramOccurrence psd, String c) {
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
    public void addRemoveContour(SpiderDiagramOccurrence psd, String c) {
        if (!removeContours.containsKey(psd)) {
            removeContours.put(psd, new HashSet<String>());
        }
        removeContours.get(psd).add(c);
    }

    public void addRemovedShading(SpiderDiagramOccurrence sd, Zone z) {
        if (!removedShading.containsKey(sd)) {
            removedShading.put(sd, new HashSet<Zone>());
        }
        removedShading.get(sd).add(z);
    }

/*    public void addRemovedShadedZones(SpiderDiagramOccurrence sd, Zone z) {
        if (!removedShadedZones.containsKey(sd)) {
            removedShadedZones.put(sd, new HashSet<Zone>());
        }
        removedShadedZones.get(sd).add(z);
    }

    public void addIntroducedShadedZones(SpiderDiagramOccurrence sd, Zone z) {
        if (!introducedShadedZones.containsKey(sd)) {
            introducedShadedZones.put(sd, new HashSet<Zone>());
        }
        introducedShadedZones.get(sd).add(z);
    }
*/

    public void addCopiedShadings(SpiderDiagramOccurrence sd, Set<Zone> z) {
        if (!copiedShadings.containsKey(sd)) {
            copiedShadings.put(sd, new HashSet<Set<Zone>>());
        }
        copiedShadings.get(sd).add(z);
    }

    public Set<Set<Zone>> getCopiedShadings(SpiderDiagramOccurrence psd) {
        if (!copiedShadings.containsKey(psd)) {
            copiedShadings.put(psd, new HashSet<Set<Zone>>());
        }
        return copiedShadings.get(psd);
    }

    public Set<String> getIntroducedContours(SpiderDiagramOccurrence psd) {
        if (!introContours.containsKey(psd)) {
            introContours.put(psd, new HashSet<String>());
        }
        return introContours.get(psd);
    }

    public Set<String> getRemovedContours(SpiderDiagramOccurrence psd) {
        if (!removeContours.containsKey(psd)) {
            removeContours.put(psd, new HashSet<String>());
        }
        return removeContours.get(psd);
    }

    public Set<Zone> getRemovedShading(SpiderDiagramOccurrence sd) {
        if (!removedShading.containsKey(sd)) {
            removedShading.put(sd, new HashSet<Zone>());
        }
        return removedShading.get(sd);

    }

/*    public Set<Zone> getRemovedShadedZones(SpiderDiagramOccurrence sd) {
        if (!removedShadedZones.containsKey(sd)) {
            removedShadedZones.put(sd, new HashSet<Zone>());
        }
        return removedShadedZones.get(sd);

    }

    public Set<Zone> getIntroducedShadedZones(SpiderDiagramOccurrence sd) {
        if (!introducedShadedZones.containsKey(sd)) {
            introducedShadedZones.put(sd, new HashSet<Zone>());
        }
        return introducedShadedZones.get(sd);

    }
    */
    public Set<String> getCopiedContours(SpiderDiagramOccurrence psd) {
        if (!copiedContours.containsKey(psd)) {
            copiedContours.put(psd, new HashSet<String>());
        }
        return copiedContours.get(psd);
    }

    public void addCopiedContour(SpiderDiagramOccurrence psd, String c) {
        if (!copiedContours.containsKey(psd)) {
            copiedContours.put(psd, new HashSet<String>());
        }
        copiedContours.get(psd).add(c);
    }

    public void removeCopiedContour(SpiderDiagramOccurrence sd, String c) {
        if (copiedContours.containsKey(sd)) {
            copiedContours.get(sd).remove(c);
        }
    }


    public void removeRemovedShading(SpiderDiagramOccurrence sd, Zone z) {
        if (removedShading.containsKey(sd)) {
            removedShading.get(sd).remove(z);
        }
    }

/*    public void removeRemoveShadedZones(SpiderDiagramOccurrence sd, Zone z) {
        if (removedShadedZones.containsKey(sd)) {
            removedShadedZones.get(sd).remove(z);
        }
    }
*/
    public  void removeRemovedContours(SpiderDiagramOccurrence sd, String c) {
 //       if (removeContours.containsKey(sd)) {
            removeContours.get(sd).remove(c);
//        }
    }

    public  void removeIntroducedContours(SpiderDiagramOccurrence sd, String c) {
        if(introContours.containsKey(sd)) {
            introContours.get(sd).remove(c);
        }
    }

    public void removeCopiedShading(SpiderDiagramOccurrence sd, Set<Zone> zones) {
        if (copiedShadings.containsKey(sd)) {
            copiedShadings.get(sd).remove(zones);
        }
    }

/*    public void removeIntroducedShadedZone(SpiderDiagramOccurrence sd, Zone z) {
        if (introducedShadedZones.containsKey(sd)) {
            introducedShadedZones.get(sd).remove(z);
        }
    }
    */
}
