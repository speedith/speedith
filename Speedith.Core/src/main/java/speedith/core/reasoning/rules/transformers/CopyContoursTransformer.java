package speedith.core.reasoning.rules.transformers;

import speedith.core.lang.*;
import speedith.core.reasoning.args.ContourArg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class CopyContoursTransformer extends IdTransformer {

    private final int indexOfParent;
    private final List<ContourArg> targetContours;

    public CopyContoursTransformer(int indexOfParent, List<ContourArg> targetContours) {
        if (indexOfParent < 0) {
            throw new TransformationException("The target sub-diagram is not in a conjunction.");
        }
        this.indexOfParent = indexOfParent;
        this.targetContours = targetContours;
    }

    public static PrimarySpiderDiagram addContoursToDiagram(PrimarySpiderDiagram diagram,
                                                            List<String> contours) {
        if (diagram.getAllContours().containsAll(contours)) {
            return diagram;
        } else if (contours.size() == 1) {
            String newContour = contours.get(0);
            return SpiderDiagrams.createPrimarySD(
                    diagram.getSpiders(),
                    diagram.getHabitats(),
                    Zones.sameRegionWithNewContours(diagram.getShadedZones(), newContour),
                    Zones.extendRegionWithNewContour(diagram.getPresentZones(), newContour)
            );
        }
        return SpiderDiagrams.createPrimarySD(diagram.getSpiders(), diagram.getHabitats(), diagram.getShadedZones(), Arrays.asList(Zone.fromInContours(contours.get(0))));
    }

    @Override
    public SpiderDiagram transform(CompoundSpiderDiagram currentDiagram,
                                   int diagramIndex,
                                   ArrayList<CompoundSpiderDiagram> parents,
                                   ArrayList<Integer> childIndices) {
        if (diagramIndex == indexOfParent) {
            assertIsConjunction(currentDiagram);
            assertOperandsAreUnitary(currentDiagram);

            PrimarySpiderDiagram diagramWithContour = getDiagramWithContour(currentDiagram);
            PrimarySpiderDiagram diagramWithoutContour = getDiagramWithoutContour(currentDiagram);

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
        PrimarySpiderDiagram transformedDiagram = addContoursToDiagram(diagramWithContour, getTargetContours());
        if (isContourInLeftDiagram()) {
            return SpiderDiagrams.createCompoundSD(Operator.Conjunction, diagramWithContour, transformedDiagram);
        } else {
            return SpiderDiagrams.createCompoundSD(Operator.Conjunction, transformedDiagram, diagramWithContour);
        }
    }

    private PrimarySpiderDiagram getDiagramWithContour(CompoundSpiderDiagram currentDiagram) {
        return (PrimarySpiderDiagram) currentDiagram.getOperand(isContourInLeftDiagram() ? 0 : 1);
    }

    private PrimarySpiderDiagram getDiagramWithoutContour(CompoundSpiderDiagram currentDiagram) {
        return (PrimarySpiderDiagram) currentDiagram.getOperand(isContourInLeftDiagram() ? 1 : 0);
    }

    private boolean isContourInLeftDiagram() {
        return getTargetSubDiagramIndex() == indexOfParent + 1;
    }

    private void assertDiagramContainsTargetContours(PrimarySpiderDiagram currentDiagram) {
        if (!currentDiagram.getAllContours().containsAll(getTargetContours())) {
            throw new TransformationException("The target unitary diagram does not contain the target contour.");
        }
    }

    private void assertIsConjunction(CompoundSpiderDiagram currentDiagram) {
        if (currentDiagram.getOperator() != Operator.Conjunction) {
            throw new TransformationException("The target unitary diagram is not conjunctively connected to another unitary diagram.");
        }
    }

    private void assertOperandsAreUnitary(CompoundSpiderDiagram compoundSpiderDiagram) {
        if (!(compoundSpiderDiagram.getOperand(0) instanceof PrimarySpiderDiagram) ||
            !(compoundSpiderDiagram.getOperand(1) instanceof PrimarySpiderDiagram)) {
            throw new TransformationException("The conjunctively connected spider diagrams are not unitary.");
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

    private int getTargetSubDiagramIndex() {
        return targetContours.get(0).getSubDiagramIndex();
    }
}
