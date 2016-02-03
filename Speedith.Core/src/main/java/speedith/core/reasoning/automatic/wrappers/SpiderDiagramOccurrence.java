package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;

import java.util.ArrayList;

/**
 * Wrapper class for SpiderDiagram classes. Adds an index
 * for each occurrence of each SpiderDiagram. Used to
 * distinguish otherwise similar SpiderDiagrams within
 * the tree structure of a SpiderDiagram
 *
 * @author Sven Linker
 *
 */
public abstract class SpiderDiagramOccurrence {

    private SpiderDiagram diagram;

    /**
     * The occurrence index of diagram.
     * This coincides with the formal SubDiagramIndex of SpiderDiagrams, but can be used
     * to refer to different occurrences of a single diagram within the same compound
     * diagram.
     */
    private int occurrenceIndex;

    public SpiderDiagramOccurrence(SpiderDiagram diagram, int occurrenceIndex) {
        this.diagram = diagram;
        this.occurrenceIndex = occurrenceIndex;
    }

    /**
     * Creates a SpiderDiagramOccurrence for the given SpiderDiagram sd to reliably
     * refer to the different occurrences of diagrams in sd
     */
    public static SpiderDiagramOccurrence wrapDiagram (SpiderDiagram sd, final int occurrenceIndex) {
        if (sd instanceof PrimarySpiderDiagram) {
            return new PrimarySpiderDiagramOccurrence(sd, occurrenceIndex);
        }
        if (sd instanceof CompoundSpiderDiagram) {
            int newIndex = occurrenceIndex+1;
            ArrayList<SpiderDiagramOccurrence> operands = new ArrayList<>();
            for(SpiderDiagram op: ((CompoundSpiderDiagram) sd).getOperands()) {
                SpiderDiagramOccurrence opWrap = wrapDiagram(op, newIndex);
                operands.add(opWrap);
                newIndex+= opWrap.getDiagram().getSubDiagramCount();
            }
            return new CompoundSpiderDiagramOccurrence(sd, occurrenceIndex, operands);

        }
        return null;
    }

    public SpiderDiagram getDiagram() {
        return diagram;
    }

    public int getOccurrenceIndex() {
        return occurrenceIndex;
    }

    @Override
    public abstract boolean equals(Object other);


}
