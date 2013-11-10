package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.Region;
import speedith.core.lang.Zone;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class CorrespondingRegionsTest {

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
}
