package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.TreeMap;

import static java.util.Arrays.asList;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static speedith.core.lang.Zones.allZonesForContours;
import static speedith.core.lang.Zones.getZonesInsideAllContours;

public class ContourRelationsInDiagramTest {

    private static final ArrayList<Zone> vennABCZones = Zones.allZonesForContours("A", "B", "C");
    private final Zone zoneAB = Zone.fromInContours("A", "B");
    private final Zone zoneB_A = Zone.fromInContours("B").withOutContours("A");
    private final ArrayList<Zone> powerRegionAB = allZonesForContours("A", "B");
    private final PrimarySpiderDiagram diagramWithContoursAB = SpiderDiagrams.createPrimarySD(null, null, null, powerRegionAB);
    private final PrimarySpiderDiagram diagramWithShadedB = SpiderDiagrams.createPrimarySD(null, null, asList(zoneB_A, zoneAB), powerRegionAB);
    private final PrimarySpiderDiagram diagramWithShadedIntersection = SpiderDiagrams.createPrimarySD(null, null, asList(zoneAB), powerRegionAB);

    @Test
    public void areContoursDisjoint_should_return_false_in_a_Venn_diagram() {
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(diagramWithContoursAB);
        assertFalse(contourRelationsInDiagram.areContoursDisjoint("A", "B"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void areContoursDisjoint_should_throw_an_exception_if_any_of_the_contours_is_not_in_the_diagram() {
        new ContourRelationsInDiagram(diagramWithContoursAB).areContoursDisjoint("C", "D");
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_zone_AsubB_is_shaded() {
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(diagramWithShadedIntersection);
        assertTrue(contourRelationsInDiagram.areContoursDisjoint("A", "B"));
    }

    @Test
    public void areContoursDisjoint_should_return_false_when_not_all_shared_zones_are_shaded() {
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(SpiderDiagrams.createPrimarySD(null, null, getZonesInsideAllContours(allZonesForContours("A", "B", "C", "D"), "A", "B", "C"), null));
        assertFalse(contourRelationsInDiagram.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_there_are_multiple_zones_and_all_shared_zones_are_shaded() {
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(SpiderDiagrams.createPrimarySD(null, null, getZonesInsideAllContours(allZonesForContours("A", "B", "C", "D"), "A", "D"), null));
        assertTrue(contourRelationsInDiagram.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_false_when_there_are_any_spiders_in_the_shared_shaded_zones() {
        TreeMap<String, Region> habitats = new TreeMap<>();
        String spider = "s";
        habitats.put(spider, new Region(Zone.fromInContours("A", "C", "D").withOutContours("B")));
        PrimarySpiderDiagram diagramWithASpiderInTheIntersection = SpiderDiagrams.createPrimarySD(asList(spider), habitats, getZonesInsideAllContours(allZonesForContours("A", "B", "C", "D"), "A", "D"), null);
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(diagramWithASpiderInTheIntersection);
        assertFalse(contourRelationsInDiagram.areContoursDisjoint("A", "D"));
    }

    @Test
    public void areContoursDisjoint_should_return_true_when_the_spiders_are_not_in_the_shared_shaded_zones() {
        TreeMap<String, Region> habitats = new TreeMap<>();
        String spider = "s";
        habitats.put(spider, new Region(Zone.fromInContours("A", "C").withOutContours("B", "D")));
        PrimarySpiderDiagram diagramWithASpiderInTheIntersection = SpiderDiagrams.createPrimarySD(asList(spider), habitats, getZonesInsideAllContours(allZonesForContours("A", "B", "C", "D"), "A", "D"), null);
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(diagramWithASpiderInTheIntersection);
        assertTrue(contourRelationsInDiagram.areContoursDisjoint("A", "D"));
    }

    @Test
    public void contourContainsAnother_should_return_false_for_a_Venn_diagram() {
        ContourRelationsInDiagram contourRelationsInDiagram = new ContourRelationsInDiagram(diagramWithContoursAB);
        assertFalse(contourRelationsInDiagram.contourContainsAnother("A", "B"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void contourContainsAnother_should_throw_an_exception_when_the_contours_are_not_contained_in_the_diagram() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(diagramWithContoursAB);
        diagramContourRelations.contourContainsAnother("A", "C");
    }

    @Test
    public void contourContainsAnother_should_return_true_when_the_other_contour_is_entirely_shaded() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(diagramWithShadedB);
        assertTrue(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_other_contour_is_not_entirely_shaded() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(getVennABCDiagramWithShadedBC());
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_other_contour_is_not_shaded() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(diagramWithContoursAB);
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_true_when_the_only_unshaded_part_of_B_is_in_A() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(getVennABCDiagramWithPartlyShadedB());
        assertTrue(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    @Test
    public void contourContainsAnother_should_return_false_when_the_only_unshaded_part_of_B_is_in_A_but_there_is_a_spider_in_B() {
        ContourRelationsInDiagram diagramContourRelations = new ContourRelationsInDiagram(getVennABCDiagramWithPartlyShadedBAndSpiderInZoneBC_A());
        assertFalse(diagramContourRelations.contourContainsAnother("A", "B"));
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithPartlyShadedB() {
        ArrayList<Zone> zonesBC = Zones.getZonesInsideAllContours(vennABCZones, "B");
        zonesBC.remove(Zone.fromInContours("A", "B", "C"));
        return SpiderDiagrams.createPrimarySD(null, null, zonesBC, vennABCZones);
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithShadedBC() {
        ArrayList<Zone> zonesBC = Zones.getZonesInsideAllContours(vennABCZones, "B", "C");
        return SpiderDiagrams.createPrimarySD(null, null, zonesBC, vennABCZones);
    }

    public static PrimarySpiderDiagram getVennABCDiagramWithPartlyShadedBAndSpiderInZoneBC_A() {
        PrimarySpiderDiagram modelDiagram = getVennABCDiagramWithPartlyShadedB();
        HashMap<String, Region> habitats = new HashMap<>();
        habitats.put("s", new Region(Zone.fromInContours("B", "C").withOutContours("A")));
        return SpiderDiagrams.createPrimarySD(asList("s"), habitats, modelDiagram.getShadedZones(), modelDiagram.getPresentZones());
    }
}
