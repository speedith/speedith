package speedith.core.reasoning.automatic;

import speedith.core.lang.Zone;
import speedith.core.reasoning.automatic.rules.*;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 *
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AppliedRules {

    private Map<SpiderDiagramOccurrence, Set<String>> introContours;

    private Map<SpiderDiagramOccurrence, Set<String>> removeContours;

    private Map<SpiderDiagramOccurrence, Set<String>> copiedContours;

    private Map<SpiderDiagramOccurrence, Set<Zone>> removedShading;

    private Map<SpiderDiagramOccurrence, Set<Set<Zone>>> copiedShadings;


    public AppliedRules() {
        introContours = new HashMap<>();
        removeContours = new HashMap<>();
        removedShading = new HashMap<>();
        copiedContours = new HashMap<>();
        copiedShadings = new HashMap<>();

    }

    public AppliedRules(AppliedRules old) {
        this.introContours = new HashMap<> ();
        for( SpiderDiagramOccurrence key: old.introContours.keySet()) {
            this.introContours.put(key, new HashSet<>(old.introContours.get(key)));
        }
        this.removeContours = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.removeContours.keySet()) {
            this.removeContours.put(key, new HashSet<>(old.removeContours.get(key)));
        }
        this.copiedContours = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.copiedContours.keySet()) {
            this.copiedContours.put(key, new HashSet<>(old.copiedContours.get(key)));
        }
        this.removedShading = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.removedShading.keySet()) {
            this.removedShading.put(key, new HashSet<>(old.removedShading.get(key)));
        }
        this.copiedShadings = new HashMap<>();
        for (SpiderDiagramOccurrence key: old.copiedShadings.keySet()) {
            this.copiedShadings.put(key, new HashSet<>(old.copiedShadings.get(key)));
        }
    }


    public void add(PossibleRuleApplication rule, SpiderDiagramOccurrence psd) {
        if (rule instanceof PossibleCopyContour) {
            add((PossibleCopyContour) rule, psd);
        } else if(rule instanceof PossibleCopyShading) {
            add((PossibleCopyShading) rule, psd);
        } else if (rule instanceof PossibleIntroduceContour) {
            add((PossibleIntroduceContour) rule, psd);
        } else  if(rule instanceof PossibleRemoveContour) {
            add((PossibleRemoveContour) rule, psd);
        } else if(rule instanceof PossibleRemoveShading) {
            add((PossibleRemoveShading) rule, psd);
        }
    }

    /**
     * Adds the contour of the given rule to the set of already introduced contours for
     * the given primary spider diagram
     *
     * @param rule the instance of introduce contour
     * @param psd the Primary Spider diagram for which the contour shall be saved
     *            as already introduced
     */
    public void add(PossibleIntroduceContour rule, SpiderDiagramOccurrence psd) {
        if (!introContours.containsKey(psd)) {
            introContours.put(psd, new HashSet<String>());
        }
        introContours.get(psd).add(rule.getContour());
    }

    /**
     * Adds a contour to the set of already removed contours for
     * the given primary spider diagram
     * @param psd the Primary Spider diagram for which the contour shall be saved
     *            as already removed
     */
    public void add(PossibleRemoveContour rule, SpiderDiagramOccurrence psd) {
        if (!removeContours.containsKey(psd)) {
            removeContours.put(psd, new HashSet<String>());
        }
        removeContours.get(psd).add(rule.getContour());
    }

    public void add(PossibleRemoveShading rule, SpiderDiagramOccurrence sd) {
        if (!removedShading.containsKey(sd)) {
            removedShading.put(sd, new HashSet<Zone>());
        }
        removedShading.get(sd).add(rule.getZone());
    }

    public void add(PossibleCopyShading rule , SpiderDiagramOccurrence sd) {
        if (!copiedShadings.containsKey(sd)) {
            copiedShadings.put(sd, new HashSet<Set<Zone>>());
        }
        copiedShadings.get(sd).add(rule.getRegion());
    }

    public void add(PossibleCopyContour rule, SpiderDiagramOccurrence sd) {
        if (!copiedContours.containsKey(sd)) {
            copiedContours.put(sd, new HashSet<String>());
        }
        copiedContours.get(sd).add(rule.getContour());
    }

    public boolean contains(PossibleRuleApplication rule, SpiderDiagramOccurrence psd) {
        if (rule instanceof PossibleCopyContour) {
            return contains((PossibleCopyContour) rule, psd);
        } else if(rule instanceof PossibleCopyShading) {
            return contains((PossibleCopyShading) rule, psd);
        } else if (rule instanceof PossibleIntroduceContour) {
            return contains((PossibleIntroduceContour) rule, psd);
        } else  if(rule instanceof PossibleRemoveContour) {
            return contains((PossibleRemoveContour) rule, psd);
        } else if(rule instanceof PossibleRemoveShading) {
            return contains((PossibleRemoveShading) rule, psd);
        }
        return false;
    }

    public boolean contains(PossibleIntroduceContour rule, SpiderDiagramOccurrence psd) {
        return introContours.containsKey(psd) && introContours.get(psd).contains(rule.getContour());
    }

    public boolean contains(PossibleRemoveContour rule, SpiderDiagramOccurrence psd) {
        return removeContours.containsKey(psd) && removeContours.get(psd).contains(rule.getContour());
    }

    public boolean contains(PossibleCopyContour rule, SpiderDiagramOccurrence psd) {
        return copiedContours.containsKey(psd) && copiedContours.get(psd).contains(rule.getContour());
    }

    public boolean contains(PossibleCopyShading rule, SpiderDiagramOccurrence psd) {
        return copiedShadings.containsKey(psd) && copiedShadings.get(psd).contains(rule.getRegion());
    }

    public boolean contains(PossibleRemoveShading rule, SpiderDiagramOccurrence psd) {
        return removedShading.containsKey(psd) && removedShading.get(psd).contains(rule.getZone());
    }

    public void remove(PossibleRuleApplication rule, SpiderDiagramOccurrence sd) {
        if (rule instanceof PossibleCopyContour) {
            remove((PossibleCopyContour) rule, sd);
        } else if(rule instanceof PossibleCopyShading) {
            remove((PossibleCopyShading) rule, sd);
        } else if (rule instanceof PossibleIntroduceContour) {
            remove((PossibleIntroduceContour) rule, sd);
        } else  if(rule instanceof PossibleRemoveContour) {
            remove((PossibleRemoveContour) rule, sd);
        } else if(rule instanceof PossibleRemoveShading) {
            remove((PossibleRemoveShading) rule, sd);
        }
    }

    public void remove(PossibleIntroduceContour rule, SpiderDiagramOccurrence sd) {
        if (introContours.containsKey(sd)) {
            introContours.get(sd).remove(rule.getContour());
        }
    }

    public void remove(PossibleRemoveContour rule, SpiderDiagramOccurrence sd) {
        if(removeContours.containsKey(sd)) {
            removeContours.get(sd).remove(rule.getContour());
        }
    }

    public void remove(PossibleRemoveShading rule, SpiderDiagramOccurrence sd) {
        if (removedShading.containsKey(sd)) {
            removedShading.get(sd).remove(rule.getZone());
        }
    }

    public void remove(PossibleCopyContour rule, SpiderDiagramOccurrence sd) {
        if (copiedContours.containsKey(sd)) {
            copiedContours.get(sd).remove(rule.getContour());
        }
    }

    public void remove(PossibleCopyShading rule, SpiderDiagramOccurrence sd) {
        if (copiedShadings.containsKey(sd)) {
            copiedShadings.get(sd).remove(rule.getRegion());
        }
    }

}
