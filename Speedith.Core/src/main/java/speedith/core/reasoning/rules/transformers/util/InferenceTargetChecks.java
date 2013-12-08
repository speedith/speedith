package speedith.core.reasoning.rules.transformers.util;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.TransformationException;

public class InferenceTargetChecks {
    public static void assertIsConjunction(CompoundSpiderDiagram currentDiagram) {
        if (currentDiagram.getOperator() != Operator.Conjunction) {
            throw new TransformationException("The target unitary diagram is not conjunctively connected to another unitary diagram.");
        }
    }

    public static void assertOperandsAreUnitary(CompoundSpiderDiagram compoundSpiderDiagram) {
        if (!(compoundSpiderDiagram.getOperand(0) instanceof PrimarySpiderDiagram) ||
            !(compoundSpiderDiagram.getOperand(1) instanceof PrimarySpiderDiagram)) {
            throw new TransformationException("The conjunctively connected spider diagrams are not unitary.");
        }
    }
}