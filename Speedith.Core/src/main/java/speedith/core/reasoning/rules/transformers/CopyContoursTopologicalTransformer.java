package speedith.core.reasoning.rules.transformers;

import speedith.core.lang.*;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks;
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction;
import speedith.core.reasoning.util.unitary.ZoneTransferTopological;

import java.util.ArrayList;
import java.util.List;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class CopyContoursTopologicalTransformer extends IdTransformer {

    private final int indexOfParent;
    private final List<ContourArg> targetContours;

    public CopyContoursTopologicalTransformer(int indexOfParent, List<ContourArg> targetContours) {
        if (indexOfParent < 0) {
            throw new TransformationException("The target sub-diagram is not in a conjunction.");
        }
        this.indexOfParent = indexOfParent;
        this.targetContours = targetContours;
    }

    @Override
    public SpiderDiagram transform(CompoundSpiderDiagram currentDiagram,
                                   int diagramIndex,
                                   ArrayList<CompoundSpiderDiagram> parents,
                                   ArrayList<Integer> childIndices) {
        if (diagramIndex == indexOfParent) {
            InferenceTargetChecks.assertIsConjunction(currentDiagram);
            InferenceTargetChecks.assertOperandsAreUnitary(currentDiagram);

            PrimarySpiderDiagram diagramWithContour = InferenceTargetExtraction.getSourceOperand(currentDiagram, indexOfParent, targetContours.get(0));
            PrimarySpiderDiagram diagramWithoutContour = InferenceTargetExtraction.getTargetOperand(currentDiagram, indexOfParent, targetContours.get(0));

            assertDiagramContainsTargetContours(diagramWithContour);

            return copyContours(diagramWithContour, diagramWithoutContour);
        }
        return null;
    }

    @Override
    public SpiderDiagram transform(PrimarySpiderDiagram csd,
                                   int diagramIndex,
                                   ArrayList<CompoundSpiderDiagram> parents,
                                   ArrayList<Integer> childIndices) {
        checkThisDiagramNotTarget(diagramIndex);
        return null;
    }

    @Override
    public SpiderDiagram transform(NullSpiderDiagram nsd,
                                   int diagramIndex,
                                   ArrayList<CompoundSpiderDiagram> parents,
                                   ArrayList<Integer> childIndices) {
        checkThisDiagramNotTarget(diagramIndex);
        return null;
    }

    private SpiderDiagram copyContours(PrimarySpiderDiagram diagramWithContour, PrimarySpiderDiagram diagramWithoutContour) {
        try {
            PrimarySpiderDiagram transformedDiagram = new ZoneTransferTopological(diagramWithContour, diagramWithoutContour).transferContour(getTargetContours().get(0));
            return InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, diagramWithContour, transformedDiagram, targetContours.get(0), indexOfParent);
        } catch (Exception e) {
            throw new TransformationException("Could not copy the contour. " + e.getMessage(), e);
        }
    }

    private void assertDiagramContainsTargetContours(PrimarySpiderDiagram currentDiagram) {
        if (!currentDiagram.getAllContours().containsAll(getTargetContours())) {
            throw new TransformationException("The target unitary diagram does not contain the target contour.");
        }
    }

    private List<String> getTargetContours() {
        ArrayList<String> contours = new ArrayList<>();
        for (ContourArg targetContour : targetContours) {
            contours.add(targetContour.getContour());
        }
        return contours;
    }

    private void checkThisDiagramNotTarget(int diagramIndex) {
        if (diagramIndex == indexOfParent) {
            throw new TransformationException("The target of the copy contour rule must be a conjunctive compound spider diagram.");
        }
    }
}
