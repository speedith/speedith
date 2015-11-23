package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;

import java.util.SortedSet;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PrimarySpiderDiagramWrapper extends SpiderDiagramWrapper {

    private boolean hashInvalid = true;
    private int hash;


    public PrimarySpiderDiagramWrapper(SpiderDiagram diagram, int occurrenceIndex) {
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

    @Override
    public boolean equals(Object other) {
        return other == this ||
                (other instanceof PrimarySpiderDiagramWrapper
                        && hashCode() == other.hashCode()
                        && getDiagram().equals(((PrimarySpiderDiagramWrapper) other).getDiagram())
                        && getOccurrenceIndex() == ((PrimarySpiderDiagramWrapper) other).getOccurrenceIndex()
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
