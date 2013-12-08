package speedith.core.reasoning.rules.transformers.util;

import speedith.core.lang.*;
import speedith.core.reasoning.args.SubDiagramIndexArg;

public class InferenceTargetExtraction {
    public static PrimarySpiderDiagram getSourceOperand(CompoundSpiderDiagram currentDiagram, int currentDiagramIndex, SubDiagramIndexArg inferenceTarget) {
        return (PrimarySpiderDiagram) currentDiagram.getOperand(isLeftOperand(inferenceTarget, currentDiagramIndex) ? 0 : 1);
    }

    public static boolean isLeftOperand(SubDiagramIndexArg treeIndexOfChild, int treeIndexOfParent) {
        return treeIndexOfChild.getSubDiagramIndex() == treeIndexOfParent + 1;
    }

    public static PrimarySpiderDiagram getTargetOperand(CompoundSpiderDiagram currentDiagram, int currentDiagramIndex, SubDiagramIndexArg inferenceTarget) {
        return (PrimarySpiderDiagram) currentDiagram.getOperand(isLeftOperand(inferenceTarget, currentDiagramIndex) ? 1 : 0);
    }

    public static SpiderDiagram createBinaryDiagram(Operator operator,
                                                    PrimarySpiderDiagram sourceDiagram,
                                                    PrimarySpiderDiagram targetDiagram,
                                                    SubDiagramIndexArg previousTargetDiagramIndex,
                                                    int previousParentIndex) {
        if (isLeftOperand(previousTargetDiagramIndex, previousParentIndex)) {
            return SpiderDiagrams.createCompoundSD(operator, sourceDiagram, targetDiagram);
        } else {
            return SpiderDiagrams.createCompoundSD(operator, targetDiagram, sourceDiagram);
        }
    }
}
