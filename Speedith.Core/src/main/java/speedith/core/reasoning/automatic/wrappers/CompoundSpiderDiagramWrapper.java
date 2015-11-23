package speedith.core.reasoning.automatic.wrappers;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.SpiderDiagram;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class CompoundSpiderDiagramWrapper extends SpiderDiagramWrapper {

    private ArrayList<SpiderDiagramWrapper> operands;

    private boolean hashInvalid = true;
    private int hash;


    public CompoundSpiderDiagramWrapper(SpiderDiagram diagram, int occurrenceIndex, ArrayList<SpiderDiagramWrapper> operands) {
        super(diagram, occurrenceIndex);
        this.operands = operands;
    }

    public List<SpiderDiagramWrapper> getOperands() {
        return Collections.unmodifiableList(operands);
    }

    public SpiderDiagramWrapper getOperand(int index) {
        return operands.get(index);
    }

    public CompoundSpiderDiagram getCompoundDiagram() {
        return (CompoundSpiderDiagram) getDiagram();
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        } else if (other instanceof CompoundSpiderDiagramWrapper) {
            return hashCode() == other.hashCode()
                    && getDiagram().equals(((CompoundSpiderDiagramWrapper) other).getDiagram())
                    ;
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = getDiagram().hashCode();
            if (operands != null) {
                for (SpiderDiagramWrapper sd : operands) {
                    hash += sd.hashCode();
                }
            }
            hash += getOccurrenceIndex();
            hashInvalid = false;
        }
        return hash;
    }


}
