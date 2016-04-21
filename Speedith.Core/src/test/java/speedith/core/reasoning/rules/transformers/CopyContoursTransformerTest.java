package speedith.core.reasoning.rules.transformers;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.args.ContourArg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static java.util.Arrays.asList;
import static org.junit.Assert.assertEquals;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;

public class CopyContoursTransformerTest {

    public static final Zone zoneBAndA = Zone.fromInContours("B", "A");
    public static final Zone zoneBMinusA = Zone.fromInContours("B").withOutContours("A");
    public static final Zone zoneAMinusB = Zone.fromInContours("A").withOutContours("B");
    public static final CompoundSpiderDiagram conjunctiveNullDiagrams = createConjunction(NullSpiderDiagram.getInstance(), NullSpiderDiagram.getInstance());
    public static final PrimarySpiderDiagram diagramWithContourA = createPrimarySD(null, null, null, asList(Zone.fromInContours("A"), Zone.fromOutContours("A")));
    public static final PrimarySpiderDiagram diagramWithASpider = createPrimarySD(asList("s"), getSpiderInRegion("s", new Region(Zone.fromInContours("A"))), null, null);

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_subdiagram_is_a_null_diagram() {
        applyCopyContoursTransform(conjunctiveNullDiagrams);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_wrong_parent_index_is_given() {
        CopyContoursTransformer copyContoursTransformer = new CopyContoursTransformer(1, asList(new ContourArg(0, 1, "A")));
        conjunctiveNullDiagrams.transform(copyContoursTransformer);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_subdiagram_is_compound() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(conjunctiveNullDiagrams, conjunctiveNullDiagrams);

        applyCopyContoursTransform(conjunctiveCompoundDiagram);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_unitary_is_not_conjunctively_connected() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createCompoundSD(
                Operator.Disjunction,
                diagramWithContourA,
                diagramWithContourA
        );

        applyCopyContoursTransform(conjunctiveCompoundDiagram);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_conjunctively_connected_diagram_is_not_unitary() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(diagramWithContourA, NullSpiderDiagram.getInstance());

        applyCopyContoursTransform(conjunctiveCompoundDiagram);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_when_target_is_on_right_hand_side_and_if_the_conjunctively_connected_diagram_is_not_unitary() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(NullSpiderDiagram.getInstance(), diagramWithContourA);

        applyCopyContoursTransform(conjunctiveCompoundDiagram, new ContourArg(0, 2, "B"));
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_unitary_diagram_does_not_have_a_parent() {
        applyCopyContoursTransform(diagramWithContourA, new ContourArg(0, 0, "A"));
    }

    @Test(expected = TransformationException.class)
    public void should_not_transform_the_diagram_if_they_share_the_same_contour() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(diagramWithContourA, diagramWithContourA);
        applyCopyContoursTransform(conjunctiveCompoundDiagram);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_unitary_diagram_does_not_contain_the_contour() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(diagramWithContourA, diagramWithContourA);

        assertEquals(
                conjunctiveCompoundDiagram,
                applyCopyContoursTransform(conjunctiveCompoundDiagram, new ContourArg(0, 1, "B"))
        );
    }

    @Test
    public void should_not_copy_the_contour_to_the_empty_primary_diagram() {
        Set<Zone> present = new HashSet<>();
        present.add(new Zone());
        CompoundSpiderDiagram nestedConjunction = createConjunction(createPrimarySD(null, null, null,present ), diagramWithContourA);
        CompoundSpiderDiagram outerConjunction = createConjunction(conjunctiveNullDiagrams, createConjunction(nestedConjunction, nestedConjunction));
        String contourToCopy = "A";
        CompoundSpiderDiagram expectedResult = createConjunction(conjunctiveNullDiagrams, createConjunction(nestedConjunction, createConjunction(diagramWithContourA, diagramWithContourA)));

        assertEquals(
                expectedResult,
                applyCopyContoursTransform(outerConjunction, new ContourArg(0, 10, contourToCopy))
        );
    }

    private static Map<String, Region> getSpiderInRegion(String spider, Region habitat) {
        HashMap<String, Region> spiderToHabitatMap = new HashMap<>();
        spiderToHabitatMap.put(spider, habitat);
        return spiderToHabitatMap;
    }

    private static CompoundSpiderDiagram createConjunction(SpiderDiagram leftHandDiagram, SpiderDiagram rightHandDiagram) {
        return createCompoundSD(
                Operator.Conjunction,
                leftHandDiagram,
                rightHandDiagram
        );
    }

    private SpiderDiagram applyCopyContoursTransform(SpiderDiagram diagramToTransform, ContourArg... rootTarget) {
        rootTarget = rootTarget.length == 0 ? new ContourArg[]{new ContourArg(0, 1, "A")} : rootTarget;
        int indexOfParent = diagramToTransform.getParentIndexOf(rootTarget[0].getSubDiagramIndex());
        CopyContoursTransformer copyContoursTransformer = new CopyContoursTransformer(indexOfParent, asList(rootTarget));
        return diagramToTransform.transform(copyContoursTransformer, true);
    }
}
