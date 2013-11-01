package speedith.core.lang;

import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;
import static speedith.core.lang.Zones.allZonesForContours;
import static speedith.core.lang.Zones.sameRegionWithNewContours;

public class ZonesTest {

    private final Zone zoneAB = Zone.fromInContours("A", "B");
    private final Zone zoneA_B = Zone.fromInContours("A").withOutContours("B");
    private final Zone zoneB_A = Zone.fromInContours("B").withOutContours("A");
    private final Zone zone_AB = Zone.fromOutContours("A", "B");
    private final List<Zone> powerRegionAB = Arrays.asList(zoneAB, zoneA_B, zoneB_A, zone_AB);

    @Test
    public void allZonesForContours_should_return_an_empty_list_of_zones_when_given_no_contours() throws Exception {
        assertEquals(new ArrayList<Zone>(), Zones.allZonesForContours());
    }

    @Test
    public void allZonesForContours_should_return_a_single_zone_when_given_a_single_contour() throws Exception {
        assertEquals(
                Arrays.asList(Zone.fromInContours("A"), Zone.fromOutContours("A")),
                Zones.allZonesForContours("A")
        );
    }

    @Test
    public void allZonesForContours_should_return_three_zones_when_given_two_contours() throws Exception {
        assertEquals(
                new HashSet<>(powerRegionAB),
                new HashSet<>(Zones.allZonesForContours("A", "B"))
        );
    }

    @Test
    public void getZonesOutsideContours_should_return_the_same_region_when_given_contours_are_not_in_zones() {
        assertEquals(
                powerRegionAB,
                Zones.getZonesOutsideContours(powerRegionAB, "D")
        );
    }

    @Test
    public void getZonesOutsideContours_should_return_only_some_zones_when_given_contours_present_in_zones() {
        assertEquals(
                Arrays.asList(zoneB_A, zone_AB),
                Zones.getZonesOutsideContours(powerRegionAB, "A")
        );
    }

    @Test
    public void testExtendRegionWithNewContour() throws Exception {

    }

    @Test
    public void sameRegionWithNewContour_should_return_an_empty_region_when_the_initial_region_is_empty() throws Exception {
        assertEquals(
                new ArrayList<Zone>(),
                Zones.sameRegionWithNewContours(new ArrayList<Zone>(), "A")
        );
    }

    @Test
    public void sameRegionWithNewContour_should_return_an_empty_region_when_given_null_region() throws Exception {
        assertEquals(
                new ArrayList<Zone>(),
                Zones.sameRegionWithNewContours(null, "A")
        );
    }

    @Test
    public void sameRegionWithNewContour_should_return_the_same_region_expressed_with_the_additional_contour() throws Exception {
        assertEquals(
                new TreeSet<>(Arrays.asList(zoneB_A, zoneAB)),
                new TreeSet<>(Zones.sameRegionWithNewContours(Arrays.asList(Zone.fromInContours("B")), "A"))
        );
    }

    @Test
    public void sameRegionWithNewContours_when_given_two_contours_should_return_the_initial_region_expressed_with_the_extended_contours() {
        assertEquals(
                new TreeSet<>(Zones.getZonesInsideContours(allZonesForContours("A", "B", "C"), "B")),
                new TreeSet<>(sameRegionWithNewContours(Arrays.asList(Zone.fromInContours("B")), "A", "C"))
        );
    }
}
