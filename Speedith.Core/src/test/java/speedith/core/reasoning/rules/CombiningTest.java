package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.lang.util.RegionBuilder;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.ArrayList;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static speedith.core.lang.Operator.Conjunction;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.lang.Zones.getZonesInsideAllContours;
import static speedith.core.lang.test.RegionsABC.*;
import static speedith.core.lang.util.HabitatBuilder.emptyHabitat;
import static speedith.core.lang.util.RegionBuilder.emptyRegion;
import static speedith.core.reasoning.Goals.createGoalsFrom;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class CombiningTest {

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_the_diagrams_have_different_contours() throws RuleApplicationException {
    PrimarySpiderDiagram leftConjunct = createPrimarySD(emptyHabitat().get(), POWER_REGION_ABD, POWER_REGION_ABD);
    PrimarySpiderDiagram rightConjunct = createPrimarySD(emptyHabitat().get(), POWER_REGION_ABC, POWER_REGION_ABC);
    applyCombining(leftConjunct, rightConjunct);
  }

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_a_spider_in_either_of_the_conjuncts_has_more_than_one_foot() throws RuleApplicationException {
    Map<String, Region> multipleFeetHabitats = emptyHabitat().addHabitat("s", getZonesInsideAllContours(POWER_REGION_AB, "A")).get();
    PrimarySpiderDiagram leftConjunct = createPrimarySD(multipleFeetHabitats, POWER_REGION_AB, POWER_REGION_AB);
    applyCombining(leftConjunct, leftConjunct);
  }

  @Test
  public void apply_MUST_return_bottom_WHEN_the_shaded_zones_in_the_two_spider_diagrams_contain_different_number_of_spiders() throws RuleApplicationException {
    ArrayList<Zone> zoneAB = getZonesInsideAllContours(POWER_REGION_AB, "A", "B");

    Map<String, Region> twoSpidersInZoneAB = emptyHabitat()
      .addHabitat("s1", zoneAB)
      .addHabitat("s2", zoneAB).get();

    Map<String, Region> oneSpidersInZoneAB = emptyHabitat()
      .addHabitat("s1", zoneAB).get();

    SpiderDiagram applicationResult = applyCombining(
      createPrimarySD(twoSpidersInZoneAB, POWER_REGION_AB, POWER_REGION_AB),
      createPrimarySD(oneSpidersInZoneAB, POWER_REGION_AB, POWER_REGION_AB)
    );

    assertEquals(SpiderDiagrams.bottom(), applicationResult);
  }

  @Test
  public void apply_MUST_return_bottom_WHEN_a_non_shaded_zone_contains_more_spiders_than_the_same_zone_in_the_other_diagram() throws RuleApplicationException {
    Map<String, Region> leftDiagramHabitat = emptyHabitat().addHabitat("s1", REGION_AB_C).get();

    SpiderDiagram applicationResult = applyCombining(
      createPrimarySD(leftDiagramHabitat, emptyRegion().asZones(), FULL_ABC_REGION.asZones()),
      createPrimarySD(emptyHabitat().get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones())
    );

    assertEquals(SpiderDiagrams.bottom(), applicationResult);
  }

  @Test
  public void apply_MUST_return_a_diagram_with_two_spiders_WHEN_one_diagram_contains_one_spider_and_the_other_one_contains_two() throws RuleApplicationException {
    Map<String, Region> leftConjunctHabitats = emptyHabitat()
      .addHabitat("s1", REGION_AB_C)
      .addHabitat("s2", REGION_AB_C).get();
    PrimarySpiderDiagram leftConjunct = createPrimarySD(leftConjunctHabitats, emptyRegion().asZones(), FULL_ABC_REGION.asZones());

    Map<String, Region> rightConjunctHabitats = emptyHabitat()
      .addHabitat("t1", REGION_AB_C).get();
    PrimarySpiderDiagram rightConjunct = createPrimarySD(rightConjunctHabitats, emptyRegion().asZones(), FULL_ABC_REGION.asZones());

    PrimarySpiderDiagram expectedResult = createPrimarySD(leftConjunctHabitats, emptyRegion().asZones(), FULL_ABC_REGION.asZones());

    assertEquals(expectedResult, applyCombining(leftConjunct, rightConjunct));
  }

  @Test
  public void apply_MUST_return_a_diagram_with_union_shading() throws RuleApplicationException {
    RegionBuilder leftConjunctShading = REGION_BC_A.union(REGION_AB_C);
    RegionBuilder rightConjunctShading = REGION_BC_A.union(REGION_C_AB);
    RegionBuilder resultingShading = rightConjunctShading.union(leftConjunctShading);

    PrimarySpiderDiagram leftConjunct = createPrimarySD(emptyHabitat().get(), leftConjunctShading.asZones(), FULL_ABC_REGION.asZones());
    PrimarySpiderDiagram rightConjunct = createPrimarySD(emptyHabitat().get(), rightConjunctShading.asZones(), FULL_ABC_REGION.asZones());
    PrimarySpiderDiagram expectedResult = createPrimarySD(emptyHabitat().get(), resultingShading.asZones(), FULL_ABC_REGION.asZones());

    assertEquals(expectedResult, applyCombining(leftConjunct, rightConjunct));
  }

  @Test
  public void apply_MUST_handle_example_in_fig12() throws RuleApplicationException {
    Map<String, Region> leftDiagramHabitats = emptyHabitat()
      .addHabitat("s1", REGION_AB_C)
      .addHabitat("s2", REGION_B_AC)
      .addHabitat("s3", REGION_ABC)
      .addHabitat("s4", REGION_BC_A)
      .addHabitat("s5", REGION_C_AB).get();
    RegionBuilder leftDiagramShading = REGION_BC_A.union(REGION_AB_C);
    PrimarySpiderDiagram leftConjunct = createPrimarySD(leftDiagramHabitats, leftDiagramShading.asZones(), FULL_ABC_REGION.asZones());

    Map<String, Region> rightDiagramHabitats = emptyHabitat()
      .addHabitat("t1", REGION_A_BC)
      .addHabitat("t2", REGION_B_AC)
      .addHabitat("t3", REGION_B_AC)
      .addHabitat("t4", REGION_BC_A)
      .addHabitat("t5", REGION_C_AB)
      .addHabitat("t6", REGION_C_AB).get();
    RegionBuilder rightDiagramShading = REGION_BC_A.union(REGION_C_AB);
    PrimarySpiderDiagram rightConjunct = createPrimarySD(rightDiagramHabitats, rightDiagramShading.asZones(), FULL_ABC_REGION.asZones());

    Map<String, Region> resultingDiagramHabitats = emptyHabitat()
      .addHabitat("s1", REGION_AB_C)
      .addHabitat("t1", REGION_A_BC)
      .addHabitat("t2", REGION_B_AC)
      .addHabitat("t3", REGION_B_AC)
      .addHabitat("s3", REGION_ABC)
      .addHabitat("s4", REGION_BC_A)
      .addHabitat("t5", REGION_C_AB)
      .addHabitat("t6", REGION_C_AB).get();
    RegionBuilder resultingShading = leftDiagramShading.union(rightDiagramShading);
    PrimarySpiderDiagram expectedResult = createPrimarySD(resultingDiagramHabitats, resultingShading.asZones(), FULL_ABC_REGION.asZones());

    assertEquals(expectedResult, applyCombining(leftConjunct, rightConjunct));
  }

  private static SpiderDiagram applyCombining(PrimarySpiderDiagram leftConjunct, PrimarySpiderDiagram rightConjunct) throws RuleApplicationException {
    return applyCombining(createCompoundSD(Conjunction, leftConjunct, rightConjunct)).getGoals().getGoalAt(0);
  }

  private static RuleApplicationResult applyCombining(SpiderDiagram spiderDiagram) throws RuleApplicationException {
    return new Combining().applyForwards(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

}