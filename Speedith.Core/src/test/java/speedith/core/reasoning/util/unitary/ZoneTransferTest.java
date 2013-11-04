package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;

import java.util.ArrayList;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.hasSize;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;

public class ZoneTransferTest {

    public static final ArrayList<Zone> vennABCZones = Zones.allZonesForContours("A", "B", "C");
    public static final ArrayList<Zone> vennABCZones_outsideB = Zones.getZonesOutsideContours(vennABCZones, "B");
    public static final PrimarySpiderDiagram diagramWithABCZones = createPrimarySD(null, null, Zones.getZonesInsideAllContours(vennABCZones_outsideB, "A"), vennABCZones);
    private final PrimarySpiderDiagram diagramWithABZones = createPrimarySD(null, null, null, asList(Zone.fromInContours("A", "B")));
    private final PrimarySpiderDiagram diagramWithBCZones = createPrimarySD(null, null, null, asList(Zone.fromOutContours("B", "C")));

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
        new ZoneTransfer(diagramWithABZones, diagramWithBCZones).destinationZonesForSourceContour("D");
    }

    @Test(expected = IllegalArgumentException.class)
    public void destinationZonesForSourceContour_should_throw_an_exception_if_the_contour_is_in_the_destination_diagram() {
        new ZoneTransfer(diagramWithABZones, diagramWithBCZones).destinationZonesForSourceContour("B");
    }

    @Test
    public void destinationZonesForSourceContour_should_return_an_empty_set_of_out_zones_for_a_venn_diagram() {
        ZoneDestinations zoneDestinations = new ZoneTransfer(diagramWithABZones, diagramWithBCZones).destinationZonesForSourceContour("A");
        assertThat(
                zoneDestinations.outZones(),
                hasSize(0)
        );
    }

    @Test
    public void destinationZonesForSourceContour_when_contour_A_is_contained_in_B_should_return_zones_outside_of_B_as_the_outZones_set() {
//        ZoneDestinations zoneDestinations = new ZoneTransfer(diagramWithABCZones, diagramWithBCZones).destinationZonesForSourceContour("A");
//        assertThat(
//                zoneDestinations.outZones(),
//                equalTo((Collection<Zone>) vennABCZones_outsideB)
//        );
    }
}
