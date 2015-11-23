package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.SpiderDiagram;

/**
 * Wrapper class for SpiderDiagram classes. Adds an index
 * for each occurrence of each SpiderDiagram. Used to
 * distinguish otherwise similar SpiderDiagrams within
 * the tree structure of a SpiderDiagram
 *
 * @author Sven Linker
 *
 */
public abstract class SpiderDiagramWrapper {

    private SpiderDiagram diagram;

    /**
     * The occurrence index of diagram.
     * This coincides with the formal SubDiagramIndex of SpiderDiagrams, but can be used
     * to refer to different occurrences of a single diagram within the same compound
     * diagram.
     */
    private int occurrenceIndex;

    public SpiderDiagramWrapper(SpiderDiagram diagram, int occurrenceIndex) {
        this.diagram = diagram;
        this.occurrenceIndex = occurrenceIndex;
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
