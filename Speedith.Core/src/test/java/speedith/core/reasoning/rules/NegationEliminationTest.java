package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.TransformationException;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.Map;

import static speedith.core.lang.Operator.Negation;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.lang.test.RegionsABC.FULL_ABC_REGION;
import static speedith.core.lang.test.RegionsABC.REGION_AB_C;
import static speedith.core.reasoning.Goals.createGoalsFrom;
import static speedith.core.reasoning.rules.test.HabitatBuilder.emptyHabitat;

public class NegationEliminationTest {

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_there_are_spiders_in_more_than_one_zone() throws RuleApplicationException {
    Map<String, Region> twoSpidersInZoneAB = emptyHabitat()
      .addHabitat("s1", REGION_AB_C)
      .addHabitat("s2", REGION_AB_C).get();

    apply(createPrimarySD(twoSpidersInZoneAB, FULL_ABC_REGION.asZones(), FULL_ABC_REGION.asZones()));
  }

  private static SpiderDiagram apply(PrimarySpiderDiagram diagramToNegate) throws RuleApplicationException {
    return apply(createCompoundSD(Negation, diagramToNegate)).getGoals().getGoalAt(0);
  }

  private static RuleApplicationResult apply(SpiderDiagram spiderDiagram) throws RuleApplicationException {
    return new NegationElimination().applyForwards(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

}