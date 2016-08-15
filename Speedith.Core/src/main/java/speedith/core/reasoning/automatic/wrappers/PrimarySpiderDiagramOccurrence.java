package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;

import java.util.SortedMap;
import java.util.SortedSet;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PrimarySpiderDiagramOccurrence extends SpiderDiagramOccurrence {

    private boolean hashInvalid = true;
    private int hash;


    public PrimarySpiderDiagramOccurrence(SpiderDiagram diagram, int occurrenceIndex) {
        super(diagram, occurrenceIndex);
    }

    public SortedSet<String> getAllContours() {
        return ((PrimarySpiderDiagram)getDiagram()).getAllContours();
    }

    public SortedSet<Zone> getShadedZones() {
        return ((PrimarySpiderDiagram) getDiagram()).getShadedZones();
    }

    public SortedSet<Zone> getPresentZones() {
        return ((PrimarySpiderDiagram) getDiagram()).getPresentZones();
    }

    public SortedMap<String, Region> getHabitats() {return ((PrimarySpiderDiagram) getDiagram()).getHabitats(); }

    public PrimarySpiderDiagram getPrimaryDiagram() { return (PrimarySpiderDiagram) getDiagram();}

    @Override
    public boolean equals(Object other) {
        return other == this ||
                (other instanceof PrimarySpiderDiagramOccurrence
                        && hashCode() == other.hashCode()
                        && getDiagram().equals(((PrimarySpiderDiagramOccurrence) other).getDiagram())
                        && getOccurrenceIndex() == ((PrimarySpiderDiagramOccurrence) other).getOccurrenceIndex()
                );

    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = (getDiagram() == null ? 0 : getDiagram().hashCode()) + getOccurrenceIndex();
            hashInvalid = false;
        }
        return hash;
    }
}
