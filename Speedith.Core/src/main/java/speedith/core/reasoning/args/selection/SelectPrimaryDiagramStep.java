package speedith.core.reasoning.args.selection;

/**
 * Created by sl542 on 10/11/15.
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
