package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class CompoundSpiderDiagramOccurrence extends SpiderDiagramOccurrence {

    private ArrayList<SpiderDiagramOccurrence> operands;

    private boolean hashInvalid = true;
    private int hash;


    public CompoundSpiderDiagramOccurrence(SpiderDiagram diagram, int occurrenceIndex, ArrayList<SpiderDiagramOccurrence> operands) {
        super(diagram, occurrenceIndex);
        this.operands = operands;
    }

    public List<SpiderDiagramOccurrence> getOperands() {
        return Collections.unmodifiableList(operands);
    }

    public SpiderDiagramOccurrence getOperand(int index) {
        return operands.get(index);
    }

    public CompoundSpiderDiagram getCompoundDiagram() {
        return (CompoundSpiderDiagram) getDiagram();
    }

    public Operator getOperator() { return  getCompoundDiagram().getOperator();}

    @Override
    public boolean equals(Object other) {
        return other == this ||
                other instanceof CompoundSpiderDiagramOccurrence &&
                        hashCode() == other.hashCode() &&
                        getDiagram().equals(((CompoundSpiderDiagramOccurrence) other).getDiagram());
    }


    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = getDiagram().hashCode();
            if (operands != null) {
                for (SpiderDiagramOccurrence sd : operands) {
                    hash += sd.hashCode();
                }
            }
            hash += getOccurrenceIndex();
            hashInvalid = false;
        }
        return hash;
    }


}
