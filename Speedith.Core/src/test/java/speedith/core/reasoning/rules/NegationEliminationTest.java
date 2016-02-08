package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.lang.util.HabitatBuilder;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.Map;

import static org.junit.Assert.assertEquals;
import static speedith.core.lang.Operator.Negation;
import static speedith.core.lang.SpiderDiagrams.*;
import static speedith.core.lang.test.RegionsABC.*;
import static speedith.core.lang.util.HabitatBuilder.emptyHabitat;
import static speedith.core.lang.util.RegionBuilder.emptyRegion;
import static speedith.core.reasoning.Goals.createGoalsFrom;

public class NegationEliminationTest {

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_the_diagram_is_a_null_diagram() throws RuleApplicationException {
    apply(createNullSD());
  }

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_the_diagram_is_a_negation_of_a_non_unitary_spider_diagram() throws RuleApplicationException {
    apply(SpiderDiagrams.createCompoundSD(Operator.Negation, createNullSD()));
  }

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_the_operator_is_not_a_negation() throws RuleApplicationException {
    apply(SpiderDiagrams.createCompoundSD(Operator.Conjunction, createPrimarySD(), createPrimarySD()));
  }

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_there_are_spiders_in_more_than_one_zone() throws RuleApplicationException {
    Map<String, Region> twoSpidersInZoneAB = emptyHabitat()
      .addHabitat("s1", REGION_AB_C)
      .addHabitat("s2", REGION_BC_A).get();

    apply(createPrimarySD(twoSpidersInZoneAB, FULL_ABC_REGION.asZones(), FULL_ABC_REGION.asZones()));
  }

  @Test
  public void apply_MUST_create_shaded_disjuncts_only_WHEN_the_zone_with_spiders_is_not_shaded() throws RuleApplicationException {
    HabitatBuilder s1Habitat = emptyHabitat().addHabitat("s1", REGION_AB_C);
    HabitatBuilder s2Habitat = emptyHabitat().addHabitat("s2", REGION_AB_C);

    PrimarySpiderDiagram inputDiagram = createPrimarySD(s1Habitat.addHabitats(s2Habitat).get(), emptyRegion().asZones(), FULL_ABC_REGION.asZones());

    SpiderDiagram expectedDiagram = createCompoundSD(
      Operator.Disjunction,
      createPrimarySD(emptyHabitat().get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones()),
      createPrimarySD(s1Habitat.get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones())
    );

    assertEquals(expectedDiagram, apply(inputDiagram));
  }

  @Test
  public void apply_MUST_also_create_an_unshaded_zone_with_one_more_spider_WHEN_the_zone_with_spiders_is_shaded() throws RuleApplicationException {
    HabitatBuilder s1Habitat = emptyHabitat().addHabitat("s1", REGION_AB_C);
    HabitatBuilder s2Habitat = emptyHabitat().addHabitat("s2", REGION_AB_C);

    HabitatBuilder habitatS1S2 = s1Habitat.addHabitats(s2Habitat);
    PrimarySpiderDiagram inputDiagram = createPrimarySD(habitatS1S2.get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones());

    SpiderDiagram expectedDiagram = createCompoundSD(
      Operator.Disjunction,
      createPrimarySD(emptyHabitat().get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones()),
      createCompoundSD(
        Operator.Disjunction,
        createPrimarySD(s1Habitat.get(), REGION_AB_C.asZones(), FULL_ABC_REGION.asZones()),
        createPrimarySD(habitatS1S2.addHabitat("s3", REGION_AB_C).get(), emptyRegion().asZones(), FULL_ABC_REGION.asZones())
      )
    );

    assertEquals(expectedDiagram, apply(inputDiagram));
  }

  private static SpiderDiagram apply(PrimarySpiderDiagram diagramToNegate) throws RuleApplicationException {
    return apply(createCompoundSD(Negation, diagramToNegate)).getGoals().getGoalAt(0);
  }

  private static RuleApplicationResult apply(SpiderDiagram spiderDiagram) throws RuleApplicationException {
    return new NegationElimination().applyForwards(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

}