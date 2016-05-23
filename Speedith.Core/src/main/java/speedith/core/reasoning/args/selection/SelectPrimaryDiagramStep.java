package speedith.core.reasoning.args.selection;

/**
 * A selection step denoting the necessity to select a single
 * primary diagram.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class SelectPrimaryDiagramStep extends SelectSubDiagramStep {

    public SelectPrimaryDiagramStep(boolean skippable) {
        super(skippable);
    }

    /**
     * Creates an unskippable step to select a primary diagram.
     */
    public SelectPrimaryDiagramStep() {
        super(false);
    }

    @Override
    public int getSelectableElements() {
        return SelectionStep.AllPrimaryElements;
    }

}
