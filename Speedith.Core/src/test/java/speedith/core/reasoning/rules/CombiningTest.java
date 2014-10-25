package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.*;
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
import static speedith.core.reasoning.Goals.createGoalsFrom;
import static speedith.core.reasoning.rules.test.HabitatBuilder.emptyHabitat;
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

  private static SpiderDiagram applyCombining(PrimarySpiderDiagram leftConjunct, PrimarySpiderDiagram rightConjunct) throws RuleApplicationException {
    return applyCombining(createCompoundSD(Conjunction, leftConjunct, rightConjunct)).getGoals().getGoalAt(0);
  }

  private static RuleApplicationResult applyCombining(SpiderDiagram spiderDiagram) throws RuleApplicationException {
    return new Combining().apply(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

}