package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;

import java.util.*;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.*;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;

public class ZoneTransferTest {

    private static final ArrayList<Zone> vennABCZones = Zones.allZonesForContours("A", "B", "C");
    private static final ArrayList<Zone> vennABDZones = Zones.allZonesForContours("A", "B", "D");
    private static final ArrayList<Zone> intersectionAC = Zones.getZonesInsideAllContours(vennABCZones, "A", "C");
    private static final PrimarySpiderDiagram diagramWithABZones = getDiagramWithABZones();
    private static final PrimarySpiderDiagram diagramWithBCZones = getDiagramWithBCZones();
    public static final PrimarySpiderDiagram vennABCDiagram = createPrimarySD(null, null, null, vennABCZones);
    public static final PrimarySpiderDiagram vennABDDiagram = createPrimarySD(null, null, null, vennABDZones);
    public static final PrimarySpiderDiagram diagramABC_shadedSetAC = createPrimarySD(null, null, intersectionAC, vennABCZones);
    public static final PrimarySpiderDiagram diagramABC_shadedSetC_A = createPrimarySD(null, null, Zones.getZonesOutsideContours(Zones.getZonesInsideAnyContour(vennABCZones, "A", "C"), "A"), vennABCZones);
    public static final PrimarySpiderDiagram diagramSpeedithPaperD1 = getDiagramSpeedithPaperD1();
    public static final PrimarySpiderDiagram diagramSpeedithPaperD2 = getDiagramSpeedithPaperD2();

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
        ZoneTransfer zoneTransfer = new ZoneTransfer(createPrimarySD(), diagramWithBCZones);
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
        ZoneTransfer zoneTransfer = new ZoneTransfer(vennABCDiagram, vennABDDiagram);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                hasSize(0)
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_should_return_all_zones_inside_A_when_A_is_disjoint_to_C() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramABC_shadedSetAC, vennABDDiagram);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                containsInAnyOrder(Zones.getZonesInsideAllContours(vennABDZones, "A").toArray())
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_should_return_all_zones_outside_A_when_A_is_contains_C() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramABC_shadedSetC_A, vennABDDiagram);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("C"),
                containsInAnyOrder(Zones.getZonesOutsideContours(vennABDZones, "A").toArray())
        );
    }

    @Test
    public void zonesInDestinationOutsideContour_when_using_diagrams_from_speedith_paper_should_return_zones_outside_E() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramSpeedithPaperD2, diagramSpeedithPaperD1);
        assertThat(
                zoneTransfer.zonesInDestinationOutsideContour("E"),
                containsInAnyOrder(
                        Zone.fromInContours("B").withOutContours("A", "D", "C"),
                        Zone.fromInContours("B", "D").withOutContours("A", "C"),
                        Zone.fromInContours("D").withOutContours("A", "B", "C"),
                        Zone.fromOutContours("A", "C", "B", "D")
                )
        );
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_an_empty_region_in_a_venn2_diagram() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(vennABCDiagram, vennABDDiagram);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("C"),
                hasSize(0)
        );
    }

    @Test(expected = IllegalArgumentException.class)
    public void zonesInDestinationInsideContour_should_throw_an_exception_if_the_contour_is_not_only_in_the_source_diagram() {
        new ZoneTransfer(vennABCDiagram, vennABDDiagram).zonesInDestinationInsideContour("A");
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_an_empty_region_in_a_venn2_diagram1() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(vennABCDiagram, vennABDDiagram);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("C"),
                hasSize(0)
        );
    }

    @Test
    public void zonesInDestinationInsideContour_should_return_zones_inside_A() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(getDiagramABCWhereCContainsA(), vennABDDiagram);
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
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramSpeedithPaperD2, diagramSpeedithPaperD1);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("E"),
                containsInAnyOrder(
                        Zone.fromInContours("A", "C").withOutContours("B", "D")
                )
        );
    }

    @Test
    public void zonesInDestinationInsideContour_when_transferring_contour_E_in_a_diagram_where_E_contains_A_and_C_should_return_all_zones_inside_A() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(getDiagramSpeedithPaperD2("E", "A"), diagramSpeedithPaperD1);
        assertThat(
                zoneTransfer.zonesInDestinationInsideContour("E"),
                containsInAnyOrder(
                        Zone.fromInContours("A", "C").withOutContours("B", "D"),
                        Zone.fromInContours("A", "D").withOutContours("B", "C"),
                        Zone.fromInContours("A").withOutContours("B", "C", "D")
                )
        );
    }

    @Test(expected = IllegalArgumentException.class)
    public void transferContour_should_throw_an_exception_if_the_source_diagram_does_not_contain_the_contour_to_transfer() {
        new ZoneTransfer(diagramWithABZones, createPrimarySD()).transferContour("C");
    }

    @Test
    public void transferContour_into_an_empty_primary_diagram_should_return_a_diagram_with_a_single_zone() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(getVenn2Diagram("A", "B"), getVenn2Diagram("B", "C"));
        assertThat(
                zoneTransfer.transferContour("A"),
                equalTo(createPrimarySD(null, null, null, Zones.allZonesForContours("A", "B", "C")))
        );
    }

    @Test
    public void transferContour_when_adding_a_contour_to_a_venn_diagram_should_produce_the_same_diagram() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(getDiagramABCWhereCContainsA(), getVenn2Diagram("B", "C"));
        assertThat(
                zoneTransfer.transferContour("A"),
                equalTo(getDiagramABCWhereCContainsA())
        );
    }

    @Test
    public void transferContour_should_create_some_shading() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(getDiagramABCWhereCContainsA(), vennABDDiagram);
        ArrayList<Zone> vennABCDZones = Zones.allZonesForContours("A", "B", "C", "D");
        ArrayList<Zone> presentZones = new ArrayList<>(Zones.sameRegionWithNewContours(vennABDZones, "C"));
        presentZones.removeAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(presentZones, "C"), "A"));
        ArrayList<Zone> shadedZones = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(vennABCDZones, "C"), "A");
        assertThat(
                zoneTransfer.transferContour("C"),
                equalTo(createPrimarySD(null, null, shadedZones, presentZones))
        );
    }

    @Test
    public void transferContour_should_create_replicate_the_example_in_Fig2() {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramSpeedithPaperD2, diagramSpeedithPaperD1);

        SortedSet<Zone> initialPresentZones = diagramSpeedithPaperD1.getPresentZones();
        ArrayList<Zone> presentZones = Zones.sameRegionWithNewContours(initialPresentZones, "E");
        presentZones.removeAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(presentZones, "A"), "E"));
        presentZones.remove(Zone.fromInContours("A", "C").withOutContours("B", "D", "E"));

        ArrayList<Zone> vennABCDEZones = Zones.allZonesForContours("A", "B", "C", "D", "E");
        TreeSet<Zone> shadedZones = new TreeSet<>();
        shadedZones.addAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(vennABCDEZones, "E"), "C"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(vennABCDEZones, "A"), "E"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "A", "B"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "B", "C"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "C", "D"));

        TreeSet<Zone> spider2Region = new TreeSet<>();
        spider2Region.addAll(Zones.getZonesInsideAllContours(presentZones, "B"));
        spider2Region.add(Zone.fromOutContours("A", "B", "C", "D", "E"));
        spider2Region.add(Zone.fromOutContours("A", "B", "C", "E").withInContours("D"));

        Map<String,Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zones.getZonesInsideAllContours(presentZones, "C")));
        habitats.put("s2", new Region(spider2Region));

        PrimarySpiderDiagram diagramWithTransferredContour = zoneTransfer.transferContour("E");

        assertThat(
                diagramWithTransferredContour,
                equalTo(createPrimarySD(diagramWithTransferredContour.getSpiders(), habitats, shadedZones, presentZones))
        );
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD2() {
        return getDiagramSpeedithPaperD2("A", "E");
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD2(String outsideContour, String insideContour) {
        String contourC = "C";
        String contourF = "F";
        ArrayList<Zone> abcdPowerRegion = Zones.allZonesForContours(outsideContour, contourF, contourC, insideContour);
        ArrayList<Zone> shaded_E_A = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(abcdPowerRegion, outsideContour), insideContour);
        ArrayList<Zone> shaded_C = Zones.getZonesInsideAllContours(abcdPowerRegion, contourC);
        ArrayList<Zone> shaded_F_ACE = Zones.getZonesInsideAnyContour(Zones.getZonesInsideAllContours(abcdPowerRegion, contourF), outsideContour, contourC, insideContour);

        TreeSet<Zone> presentZones = new TreeSet<>(abcdPowerRegion);
        presentZones.removeAll(shaded_E_A);
        presentZones.removeAll(shaded_C);
        presentZones.removeAll(shaded_F_ACE);

        TreeSet<Zone> shadedZones = new TreeSet<>();
        shadedZones.addAll(shaded_E_A);
        shadedZones.addAll(shaded_C);
        shadedZones.addAll(shaded_F_ACE);

        TreeMap<String, Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zone.fromInContours(outsideContour, insideContour, contourC).withOutContours(contourF)));
        habitats.put("s2", new Region(
                Zone.fromInContours(contourF).withOutContours(outsideContour, contourC, insideContour),
                Zone.fromOutContours(outsideContour, contourC, insideContour, contourF)
        ));
        habitats.put("s3", new Region(
                Zone.fromInContours(contourF).withOutContours(outsideContour, contourC, insideContour),
                Zone.fromOutContours(outsideContour, contourC, insideContour, contourF)
        ));

        return createPrimarySD(habitats.keySet(), habitats, shadedZones, presentZones);
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD1() {
        ArrayList<Zone> abcdPowerRegion = Zones.allZonesForContours("A", "B", "C", "D");
        ArrayList<Zone> shaded_C_A = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(abcdPowerRegion, "A"), "C");
        ArrayList<Zone> shaded_CBD = Zones.getZonesInsideAnyContour(Zones.getZonesInsideAnyContour(abcdPowerRegion, "B", "D"), "C");
        ArrayList<Zone> shaded_AB = Zones.getZonesInsideAllContours(abcdPowerRegion, "A", "B");

        TreeSet<Zone> presentZones = new TreeSet<>(abcdPowerRegion);
        presentZones.removeAll(shaded_C_A);
        presentZones.removeAll(shaded_CBD);
        presentZones.removeAll(shaded_AB);
        presentZones.removeAll(shaded_AB);

        TreeSet<Zone> shadedZones = new TreeSet<>(shaded_C_A);
        shadedZones.addAll(shaded_CBD);
        shadedZones.addAll(shaded_AB);

        TreeMap<String, Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zone.fromInContours("A", "C").withOutContours("B", "D")));
        habitats.put("s2", new Region(
                Zone.fromInContours("B", "D").withOutContours("A", "C"),
                Zone.fromInContours("D").withOutContours("B", "A", "C"),
                Zone.fromInContours("B").withOutContours("D", "A", "C"),
                Zone.fromOutContours("B", "D", "A", "C")
        ));

        return createPrimarySD(habitats.keySet(), habitats, shadedZones, presentZones);
    }

    public static PrimarySpiderDiagram getDiagramABCWhereCContainsA() {
        ArrayList<Zone> zonesInsideAC_outsideC = Zones.getZonesOutsideContours(Zones.getZonesInsideAnyContour(vennABCZones, "A", "C"), "C");

        TreeSet<Zone> presentZones = new TreeSet<>(vennABCZones);
        presentZones.removeAll(zonesInsideAC_outsideC);

        return createPrimarySD(null, null, zonesInsideAC_outsideC, presentZones);
    }

    public static PrimarySpiderDiagram getVenn2Diagram(String contour1, String contour2) {
        return createPrimarySD(null, null, null, Zones.allZonesForContours(contour1, contour2));
    }

    public static PrimarySpiderDiagram getVenn3Diagram(String contour1, String contour2, String contour3) {
        return createPrimarySD(null, null, null, Zones.allZonesForContours(contour1, contour2, contour3));
    }

    private static PrimarySpiderDiagram getDiagramWithBCZones() {
        return createPrimarySD(null, null, null, asList(Zone.fromOutContours("B", "C")));
    }

    private static PrimarySpiderDiagram getDiagramWithABZones() {
        return createPrimarySD(null, null, null, asList(Zone.fromInContours("A", "B")));
    }
}
