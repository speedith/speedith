package speedith.core.reasoning.rules.transformers;

import speedith.core.lang.*;
import speedith.core.reasoning.args.ContourArg;

import java.util.*;

import static speedith.core.lang.Zones.sameRegionWithNewContours;

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
                                                            List<String> newContours) {
        SortedSet<String> oldContours = diagram.getAllContours();
        if (oldContours.containsAll(newContours)) {
            return diagram;
        } else if (newContours.size() == 1) {
            String newContour = newContours.get(0);
            return SpiderDiagrams.createPrimarySD(
                    diagram.getSpiders(),
                    getHabitatsWithAddedContours(diagram, newContour),
                    Zones.sameRegionWithNewContours(diagram.getShadedZones(), newContour),
                    Zones.extendRegionWithNewContour(diagram.getPresentZones(), newContour, oldContours)
            );
        }
        return SpiderDiagrams.createPrimarySD(diagram.getSpiders(), diagram.getHabitats(), diagram.getShadedZones(), Arrays.asList(Zone.fromInContours(newContours.get(0))));
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

            return copyContours(diagramWithContour);
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

    private static SortedMap<String, Region> getHabitatsWithAddedContours(PrimarySpiderDiagram diagram, String newContour) {
        SortedMap<String, Region> habitats = diagram.getHabitats();
        if (habitats == null || habitats.isEmpty()) {
            return habitats;
        }
        TreeMap<String, Region> extendedHabitats = new TreeMap<>(habitats);
        for (Map.Entry<String, Region> spiderRegion : extendedHabitats.entrySet()) {
            spiderRegion.setValue(new Region(sameRegionWithNewContours(spiderRegion.getValue().getZones(), newContour)));
        }
        return extendedHabitats;
    }

    private SpiderDiagram copyContours(PrimarySpiderDiagram diagramWithContour) {
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
