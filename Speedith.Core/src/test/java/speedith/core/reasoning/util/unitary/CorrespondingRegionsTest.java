package speedith.core.reasoning.util.unitary;

import org.junit.Ignore;
import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.Zone;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class CorrespondingRegionsTest {

    public static final PrimarySpiderDiagram SINGLE_CONTOUR_A_DIAGRAM = createPrimarySD(null, null, null, asList(Zone.fromInContours("A")));

    @Test
    public void areRegionsCorresponding_should_return_true_for_empty_regions() {
        CorrespondingRegions correspondingRegions = new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_2_AB_DIAGRAM);
        assertTrue(correspondingRegions.areRegionsCorresponding(new Region(), new Region()));
    }

    @Test(expected = IllegalArgumentException.class)
    public void areRegionsCorresponding_should_throw_an_exception_if_the_source_region_contains_unknown_contours() {
        CorrespondingRegions correspondingRegions = new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_2_AB_DIAGRAM);
        Region regionA = new Region(Zone.fromInContours("D"));
        correspondingRegions.areRegionsCorresponding(regionA, new Region());
    }

    @Test(expected = IllegalArgumentException.class)
    public void areRegionsCorresponding_should_throw_an_exception_if_the_destination_region_contains_unknown_contours() {
        CorrespondingRegions correspondingRegions = new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_2_AB_DIAGRAM);
        Region regionB = new Region(Zone.fromOutContours("C"));
        correspondingRegions.areRegionsCorresponding(new Region(), regionB);
    }

    @Test(expected = IllegalArgumentException.class)
    public void correspondingRegion_should_throw_an_exception_if_any_of_the_zones_has_a_contour_not_in_source_diagram() {
        new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM).correspondingRegion(new Region(
                Zone.fromInContours("A", "B", "C", "D")
        ));
    }

    @Test(expected = IllegalArgumentException.class)
    public void correspondingRegion_should_throw_an_exception_if_any_of_the_zones_has_a_contour_too_few_contours() {
        new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM).correspondingRegion(new Region(
                Zone.fromInContours("A", "B")
        ));
    }

    @Test
    public void correspondingRegion_of_a_single_venn3_zone_should_return_a_combinatorial_set_of_zones() {
        Region correspondingRegion = new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_2_AB_DIAGRAM).correspondingRegion(new Region(
                Zone.fromInContours("A", "C").withOutContours("B"),
                Zone.fromInContours("B", "C").withOutContours("A"),
                Zone.fromInContours("A").withOutContours("B", "C"),
                Zone.fromInContours("B").withOutContours("A", "C")
        ));

        Region expectedRegion = new Region(
                Zone.fromInContours("A").withOutContours("B"),
                Zone.fromInContours("B").withOutContours("A")
        );

        assertThat(
                correspondingRegion,
                equalTo(expectedRegion)
        );
    }

    @Test
    @Ignore
    public void correspondingRegion_of_the_outside_of_a_single_contour_must_return_every_zone_outside_that_contour_in_the_other_diagram() {
        CorrespondingRegions correspondingRegions = new CorrespondingRegions(SINGLE_CONTOUR_A_DIAGRAM, VENN_3_ABC_DIAGRAM);
        Region correspondingRegion = correspondingRegions.correspondingRegion(new Region(
                Zone.fromOutContours("A")
        ));

        Region expectedRegion = new Region(
                Zone.fromInContours("B", "C").withOutContours("A"),
                Zone.fromInContours("B").withOutContours("A", "C"),
                Zone.fromInContours("C").withOutContours("A", "B"),
                Zone.fromOutContours("A", "B", "C")
        );

        assertThat(correspondingRegion, equalTo(expectedRegion));

    }
}
