package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;
import speedith.core.lang.reader.ReadingException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.*;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class ZoneTransferTest {

    private static final ArrayList<Zone> intersectionAC = Zones.getZonesInsideAllContours(POWER_REGION_ABC, "A", "C");
    private static final PrimarySpiderDiagram diagramWithABZones = getDiagramWithABZones();
    private static final PrimarySpiderDiagram diagramWithBCZones = getDiagramWithBCZones();
    public static final PrimarySpiderDiagram diagramABC_shadedSetAC = createPrimarySD(null, null, intersectionAC, POWER_REGION_ABC);
    public static final PrimarySpiderDiagram diagramABC_shadedSetC_A = createPrimarySD(null, null, Zones.getZonesOutsideContours(Zones.getZonesInsideAnyContour(POWER_REGION_ABC, "A", "C"), "A"), POWER_REGION_ABC);

    @Test
    public void contoursOnlyInSource_returns_the_contour_that_is_present_in_the_source_diagram_but_not_in_the_destination_diagram() throws Exception {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramWithABZones, diagramWithBCZones);
        assertThat(
                zoneTransfer.contoursOnlyInSource(),
                contains("A")
        );
    }

    @Test
    public void contoursOnlyInSource_returns_an_empty_set_when_the_source_diagram_has_no_contours() throws Exception {
        Set<Zone> present = new HashSet<>();
        present.add(new Zone());
        ZoneTransfer zoneTransfer = new ZoneTransfer(createPrimarySD(null,null,null,present), diagramWithBCZones);
        assertThat(
                zoneTransfer.contoursOnlyInSource(),
                hasSize(0)
        );
    }

    @Test(expected = IllegalArgumentException.class)
    public void destinationZonesForSourceContour_should_throw_an_exception_if_the_contour_is_not_in_the_source_diagram() {
        new ZoneTransfer(diagramWithABZones, diagramWithBCZones).zonesInDestinationOutsideContour("D");
    }

    @Test(expected = IllegalArgumentException.class)
    public void destinationZonesForSourceContour_should_throw_an_exception_if_the_contour_is_in_the_destination_diagram() {
        new ZoneTransfer(diagramWithABZones, diagramWithBCZones).zonesInDestinationOutsideContour("B");
    }

    @Test
    public void zonesInDestinationOutsideContour_should_return_an_empty_set_for_two_Venn_diagrams() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                hasSize(0)
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_should_return_all_zones_inside_A_when_A_is_disjoint_to_C() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramABC_shadedSetAC, VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                containsInAnyOrder(Zones.getZonesInsideAllContours(POWER_REGION_ABD, "A").toArray())
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_should_return_all_zones_outside_A_when_A_is_contains_C() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramABC_shadedSetC_A, VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                containsInAnyOrder(Zones.getZonesOutsideContours(POWER_REGION_ABD, "A").toArray())
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_when_using_diagrams_from_speedith_paper_should_return_zones_outside_E() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D2, TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D1);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("E"),
                containsInAnyOrder(Zones.getZonesOutsideContours(POWER_REGION_ABCD, "A").toArray())
        );
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_an_empty_region_in_a_venn2_diagram() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("C"),
                hasSize(0)
        );
    }

    @Test(expected = IllegalArgumentException.class)
    public void zonesInDestinationInsideContour_should_throw_an_exception_if_the_contour_is_not_only_in_the_source_diagram() {
        new ZoneTransfer(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM).zonesInDestinationInsideContour("A");
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_an_empty_region_in_a_venn2_diagram1() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(VENN_3_ABC_DIAGRAM, VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("C"),
                hasSize(0)
        );
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_zones_inside_A() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.getDiagramABCWhereCContainsA(), VENN_3_ABD_DIAGRAM);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("C"),
                containsInAnyOrder(
                        Zone.fromInContours("A").withOutContours("B", "D"),
                        Zone.fromInContours("A", "B").withOutContours("D"),
                        Zone.fromInContours("A", "D").withOutContours("B"),
                        Zone.fromInContours("A", "B", "D").withOutContours()
                )
        );
    }

    @Test
    public void zonesInDestinationInsideContour_when_transferring_contour_E_in_diagrams_from_speedith_paper_should_return_zones_inside_AC() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D2, TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D1);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("E"),
                containsInAnyOrder(
                        Zones.getZonesInsideAllContours(POWER_REGION_ABCD, "C").toArray()
//                        Zone.fromInContours("A", "C").withOutContours("B", "D")
                )
        );
    }

    @Test
    public void zonesInDestinationInsideContour_when_transferring_contour_E_in_a_diagram_where_E_contains_A_and_C_should_return_all_zones_inside_A() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.getDiagramSpeedithPaper_Fig2_D2("E", "A"), TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D1);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("E"),
                containsInAnyOrder(Zones.getZonesInsideAnyContour(POWER_REGION_ABCD, "A", "C").toArray())
        );
    }

    @Test(expected = IllegalArgumentException.class)
    public void transferContour_should_throw_an_exception_if_the_source_diagram_does_not_contain_the_contour_to_transfer() {
        Set<Zone> present = new HashSet<>();
        present.add(new Zone());
        new ZoneTransfer(diagramWithABZones, createPrimarySD(null,null,null,present)).transferContour("C");
    }

    @Test
    public void transferContour_into_an_empty_primary_diagram_should_return_a_diagram_with_a_single_zone() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.getVenn2Diagram("A", "B"), TestSpiderDiagrams.getVenn2Diagram("B", "C"));
        assertThat(
                zoneTransfer.transferContour("A"),
                equalTo(VENN_3_ABC_DIAGRAM)
        );
    }

    @Test
    public void transferContour_when_adding_a_contour_to_a_venn_diagram_should_produce_the_same_diagram() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.getDiagramABCWhereCContainsA(), TestSpiderDiagrams.getVenn2Diagram("B", "C"));
        assertThat(
                zoneTransfer.transferContour("A"),
                equalTo(TestSpiderDiagrams.getDiagramABCWhereCContainsA())
        );
    }

    @Test
    public void transferContour_should_create_some_shading() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(TestSpiderDiagrams.getDiagramABCWhereCContainsA(), VENN_3_ABD_DIAGRAM);
        ArrayList<Zone> presentZones = new ArrayList<>(Zones.sameRegionWithNewContours(POWER_REGION_ABD, "C"));
        presentZones.removeAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(presentZones, "C"), "A"));
        ArrayList<Zone> shadedZones = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(POWER_REGION_ABCD, "C"), "A");
        assertThat(
                zoneTransfer.transferContour("C"),
                equalTo(createPrimarySD(null, null, shadedZones, presentZones))
        );
    }

    @Test
    public void transferContour_should_create_replicate_the_example_in_Fig2() throws ReadingException, IOException {
        ZoneTransfer zoneTransfer = new ZoneTransfer(DIAGRAM_SPEEDITH_PAPER_FIG7_2,
                                                     DIAGRAM_SPEEDITH_PAPER_FIG7_1);

        PrimarySpiderDiagram expectedDiagram = DIAGRAM_SPEEDITH_PAPER_FIG7_3;

        PrimarySpiderDiagram diagramWithTransferredContour = zoneTransfer.transferContour("D");

        assertThat(
                diagramWithTransferredContour.getShadedZones(),
                equalTo(expectedDiagram.getShadedZones())
        );
        assertThat(
                diagramWithTransferredContour.getHabitats(),
                equalTo(expectedDiagram.getHabitats())
        );
        assertThat(
                diagramWithTransferredContour.getPresentZones(),
                contains(
                        Zone.fromOutContours("A","B","C","D"),
                        Zone.fromInContours("C").withOutContours("A", "B", "D"),
                        Zone.fromInContours("C", "D").withOutContours("A", "B")

                )
        );
    }

    @Test
    public void transferContour_should_replicate_the_first_step_in_Fig2_of_the_Speedith_paper() {

    }

    private static PrimarySpiderDiagram getDiagramWithBCZones() {
        return createPrimarySD(null, null, null, asList(Zone.fromOutContours("B", "C")));
    }

    private static PrimarySpiderDiagram getDiagramWithABZones() {
        return createPrimarySD(null, null, null, asList(Zone.fromInContours("A", "B"), Zone.fromOutContours("A","B")));
    }
}
