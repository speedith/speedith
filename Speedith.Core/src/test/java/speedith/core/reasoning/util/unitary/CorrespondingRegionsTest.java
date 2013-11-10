package speedith.core.reasoning.util.unitary;

import org.junit.Ignore;
import org.junit.Test;
import speedith.core.lang.Region;
import speedith.core.lang.Zone;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.Zones.getZonesInsideAllContours;
import static speedith.core.lang.Zones.getZonesOutsideContours;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.POWER_REGION_ABD;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.VENN_3_ABC_DIAGRAM;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.VENN_3_ABD_DIAGRAM;

public class CorrespondingRegionsTest {

    @Test(expected = IllegalArgumentException.class)
    public void correspondingRegion_should_throw_an_exception_if_any_of_the_zones_has_a_contour_not_in_source_diagram() {
        new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM).correspondingRegion(new Region(
                Zone.fromInContours("A", "D")
        ));
    }

    @Test
    @Ignore
    public void correspondingRegion_of_a_single_venn3_zone_should_return_a_combinatorial_set_of_zones() {
        Region correspondingRegion = new CorrespondingRegions(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM).correspondingRegion(new Region(
                Zone.fromInContours("A", "C").withOutContours("B")
        ));

        Region expectedRegion = new Region(
                getZonesOutsideContours(getZonesInsideAllContours(POWER_REGION_ABD, "A"), "B")
        );

        assertThat(
                correspondingRegion,
                equalTo(expectedRegion)
        );
    }
}
