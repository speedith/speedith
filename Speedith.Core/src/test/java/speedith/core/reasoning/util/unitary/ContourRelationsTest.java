package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import propity.util.Sets;
import speedith.core.lang.*;

import java.util.*;

import static java.util.Arrays.asList;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static speedith.core.lang.Zones.allZonesForContours;
import static speedith.core.lang.Zones.getZonesInsideAllContours;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.POWER_REGION_ABC;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.POWER_REGION_ABCD;

public class ContourRelationsTest {

    private final Zone zoneAB = Zone.fromInContours("A", "B");
    private final Zone zoneB_A = Zone.fromInContours("B").withOutContours("A");
    private final ArrayList<Zone> powerRegionAB = allZonesForContours("A", "B");
    private final PrimarySpiderDiagram diagramWithContoursAB = SpiderDiagrams.createPrimarySD(null, null, null, powerRegionAB);
    private final PrimarySpiderDiagram diagramWithShadedB = SpiderDiagrams.createPrimarySD(null, null, asList(zoneB_A, zoneAB), powerRegionAB);
    private final PrimarySpiderDiagram diagramWithShadedIntersection = SpiderDiagrams.createPrimarySD(null, null, asList(zoneAB), powerRegionAB);

    @Test
    public void areContoursDisjoint_should_return_false_in_a_Venn_diagram() {
        ContourRelations contourRelations = new ContourRelations(diagramWithContoursAB);
        assertFalse(contourRelations.areContoursDisjoint("A", "B"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void areContoursDisjoint_should_throw_an_exception_if_any_of_the_contours_is_not_in_the_diagram() {
        new ContourRelations(diagramWithContoursAB).areContoursDisjoint("C", "D");
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_zone_AsubB_is_shaded() {
        ContourRelations contourRelations = new ContourRelations(diagramWithShadedIntersection);
        assertTrue(contourRelations.areContoursDisjoint("A", "B"));
    }

    @Test
    public void areContoursDisjoint_should_return_false_when_not_all_shared_zones_are_shaded() {
        Set<Zone> present = new HashSet<>();
        present.add(Zone.fromOutContours("A","B","C","D"));
        ContourRelations contourRelations = new ContourRelations(SpiderDiagrams.createPrimarySD(null, null, getZonesInsideAllContours(POWER_REGION_ABCD, "A", "B", "C"), present));
        assertFalse(contourRelations.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_there_are_multiple_zones_and_all_shared_zones_are_shaded() {
        Set<Zone> present = new HashSet<>();
        present.add(Zone.fromOutContours("A","B","C","D"));
        ContourRelations contourRelations = new ContourRelations(SpiderDiagrams.createPrimarySD(null, null, getZonesInsideAllContours(POWER_REGION_ABCD, "A", "D"), present));
        assertTrue(contourRelations.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_false_when_there_are_any_spiders_in_the_shared_shaded_zones() {
        TreeMap<String, Region> habitats = new TreeMap<>();
        String spider = "s";
        habitats.put(spider, new Region(Zone.fromInContours("A", "C", "D").withOutContours("B")));
        Set<Zone> present = new HashSet<>();
        present.add(Zone.fromOutContours("A","B","C","D"));
        PrimarySpiderDiagram diagramWithASpiderInTheIntersection = SpiderDiagrams.createPrimarySD(asList(spider), habitats, getZonesInsideAllContours(POWER_REGION_ABCD, "A", "D"), present);
        ContourRelations contourRelations = new ContourRelations(diagramWithASpiderInTheIntersection);
        assertFalse(contourRelations.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_the_spiders_are_not_in_the_shared_shaded_zones() {
        TreeMap<String, Region> habitats = new TreeMap<>();
        String spider = "s";
        habitats.put(spider, new Region(Zone.fromInContours("A", "C").withOutContours("B", "D")));
        Set<Zone> present = new HashSet<>();
        present.add(Zone.fromOutContours("A","B","C","D"));
        PrimarySpiderDiagram diagramWithASpiderInTheIntersection = SpiderDiagrams.createPrimarySD(asList(spider), habitats, getZonesInsideAllContours(POWER_REGION_ABCD, "A", "D"), present);
        ContourRelations contourRelations = new ContourRelations(diagramWithASpiderInTheIntersection);
        assertTrue(contourRelations.areContoursDisjoint("A", "D"));
    }

    @Test
    public void contourContainsAnother_should_return_false_for_a_Venn_diagram() {
        ContourRelations contourRelations = new ContourRelations(diagramWithContoursAB);
        assertFalse(contourRelations.contourContainsAnother("A", "B"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void contourContainsAnother_should_throw_an_exception_when_the_contours_are_not_contained_in_the_diagram() {
        ContourRelations diagramContourRelations = new ContourRelations(diagramWithContoursAB);
        diagramContourRelations.contourContainsAnother("A", "C");
    }

    @Test
    public void contourContainsAnother_should_return_true_when_the_other_contour_is_entirely_shaded() {
        ContourRelations diagramContourRelations = new ContourRelations(diagramWithShadedB);
        assertTrue(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_other_contour_is_not_entirely_shaded() {
        ContourRelations diagramContourRelations = new ContourRelations(getVennABCDiagramWithShadedBC());
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_other_contour_is_not_shaded() {
        ContourRelations diagramContourRelations = new ContourRelations(diagramWithContoursAB);
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_true_when_the_only_unshaded_part_of_B_is_in_A() {
        ContourRelations diagramContourRelations = new ContourRelations(getVennABCDiagramWithPartlyShadedB());
        assertTrue(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_only_unshaded_part_of_B_is_in_A_but_there_is_a_spider_in_B() {
        ContourRelations diagramContourRelations = new ContourRelations(getVennABCDiagramWithPartlyShadedBAndSpiderInZoneBC_A());
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithPartlyShadedB() {
        ArrayList<Zone> zonesBC = Zones.getZonesInsideAllContours(POWER_REGION_ABC, "B");
        zonesBC.remove(Zone.fromInContours("A", "B", "C"));
        return SpiderDiagrams.createPrimarySD(null, null, zonesBC, POWER_REGION_ABC);
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithShadedBC() {
        ArrayList<Zone> zonesBC = Zones.getZonesInsideAllContours(POWER_REGION_ABC, "B", "C");
        return SpiderDiagrams.createPrimarySD(null, null, zonesBC, POWER_REGION_ABC);
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithPartlyShadedBAndSpiderInZoneBC_A() {
        PrimarySpiderDiagram modelDiagram = getVennABCDiagramWithPartlyShadedB();
        HashMap<String, Region> habitats = new HashMap<>();
        habitats.put("s", new Region(Zone.fromInContours("B", "C").withOutContours("A")));
        return SpiderDiagrams.createPrimarySD(asList("s"), habitats, modelDiagram.getShadedZones(), modelDiagram.getPresentZones());
    }
}
