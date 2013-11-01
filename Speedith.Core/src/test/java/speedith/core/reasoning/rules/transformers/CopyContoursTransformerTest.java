package speedith.core.reasoning.rules.transformers;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.args.ContourArg;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;

public class CopyContoursTransformerTest {

    public static final PrimarySpiderDiagram diagramWithShadedContourB = SpiderDiagrams.createPrimarySD(null, null, Arrays.asList(Zone.fromInContours("B")), null);
    public static final Zone zoneBAndA = Zone.fromInContours("B", "A");
    public static final Zone zoneBMinusA = Zone.fromInContours("B").withOutContours("A");
    public static final Zone zoneAMinusB = Zone.fromInContours("A").withOutContours("B");
    private final CompoundSpiderDiagram conjunctiveNullDiagrams = createConjunction(NullSpiderDiagram.getInstance(), NullSpiderDiagram.getInstance());
    private final PrimarySpiderDiagram diagramWithContourA = SpiderDiagrams.createPrimarySD(null, null, null, Arrays.asList(Zone.fromInContours("A")));
    private final ContourArg targetContour = new ContourArg(0, 1, "A");

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_subdiagram_is_a_null_diagram() {
        applyCopyContoursTransform(conjunctiveNullDiagrams);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_wrong_parent_index_is_given() {
        CopyContoursTransformer copyContoursTransformer = new CopyContoursTransformer(1, Arrays.asList(targetContour));
        conjunctiveNullDiagrams.transform(copyContoursTransformer);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_the_target_subdiagram_is_compound() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(conjunctiveNullDiagrams, conjunctiveNullDiagrams);

        applyCopyContoursTransform(conjunctiveCompoundDiagram);
    }

    @Test(expected = TransformationException.class)
    public void should_throw_an_exception_if_unitary_is_not_conjunctively_connected() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = SpiderDiagrams.createCompoundSD(
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

    @Test
    public void should_not_transform_the_diagram_if_they_share_the_same_contour() {
        CompoundSpiderDiagram conjunctiveCompoundDiagram = createConjunction(diagramWithContourA, diagramWithContourA);

        assertEquals(
                conjunctiveCompoundDiagram,
                applyCopyContoursTransform(conjunctiveCompoundDiagram)
        );
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
    public void should_transform_the_non_root_target_diagram() {
        CompoundSpiderDiagram nestedConjunction = createConjunction(SpiderDiagrams.createPrimarySD(), diagramWithContourA);
        CompoundSpiderDiagram outerConjunction = createConjunction(conjunctiveNullDiagrams, createConjunction(nestedConjunction, nestedConjunction));
        CompoundSpiderDiagram expectedResult = createConjunction(conjunctiveNullDiagrams, createConjunction(nestedConjunction, createConjunction(diagramWithContourA, diagramWithContourA)));

        assertEquals(
                expectedResult,
                applyCopyContoursTransform(outerConjunction, new ContourArg(0, 10, "A"))
        );
    }

    @Test
    public void copyContours_should_copy_the_single_contour_to_the_empty_spider_diagram() {
        PrimarySpiderDiagram expectedDiagram = SpiderDiagrams.createPrimarySD(null, null, null, Arrays.asList(Zone.fromInContours("A")));

        PrimarySpiderDiagram transformedDiagram = CopyContoursTransformer.addContoursToDiagram(
                SpiderDiagrams.createPrimarySD(),
                Arrays.asList("A")
        );

        assertEquals(
                expectedDiagram,
                transformedDiagram
        );
    }

    @Test
    public void copyContours_should_update_shaded_zones_with_the_new_contour() {
        PrimarySpiderDiagram expectedDiagram = SpiderDiagrams.createPrimarySD(null, null, Arrays.asList(zoneBMinusA, zoneBAndA), Arrays.asList(zoneBAndA, zoneAMinusB));

        assertEquals(expectedDiagram, CopyContoursTransformer.addContoursToDiagram(diagramWithShadedContourB, Arrays.asList("A")));
    }

    @Test
    public void copyContours_should_extend_present_zones_with_the_new_contour() {
    }

    private CompoundSpiderDiagram createConjunction(SpiderDiagram leftHandDiagram, SpiderDiagram rightHandDiagram) {
        return SpiderDiagrams.createCompoundSD(
                Operator.Conjunction,
                leftHandDiagram,
                rightHandDiagram
        );
    }

    private SpiderDiagram applyCopyContoursTransform(SpiderDiagram diagramToTransform, ContourArg... rootTarget) {
        rootTarget = rootTarget.length == 0 ? new ContourArg[]{targetContour} : rootTarget;
        int indexOfParent = diagramToTransform.getParentIndexOf(rootTarget[0].getSubDiagramIndex());
        CopyContoursTransformer copyContoursTransformer = new CopyContoursTransformer(indexOfParent, Arrays.asList(rootTarget));
        return diagramToTransform.transform(copyContoursTransformer, true);
    }
}
