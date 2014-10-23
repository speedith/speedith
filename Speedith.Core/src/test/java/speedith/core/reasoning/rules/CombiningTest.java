package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import static java.util.Arrays.asList;
import static speedith.core.lang.Operator.Conjunction;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.lang.Zones.allZonesForContours;
import static speedith.core.lang.Zones.getZonesInsideAllContours;
import static speedith.core.reasoning.Goals.createGoalsFrom;
import static speedith.core.reasoning.rules.test.HabitatBuilder.emptyHabitat;

public class CombiningTest {

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_the_diagrams_have_different_contours() throws RuleApplicationException {
    List<Zone> leftConjunctZones = allZonesForContours("A", "B");
    List<Zone> rightConjunctZones = allZonesForContours("A", "C");
    PrimarySpiderDiagram leftConjunct = createPrimarySD(Collections.<String>emptyList(), emptyHabitat().get(), leftConjunctZones, leftConjunctZones);
    PrimarySpiderDiagram rightConjunct = createPrimarySD(Collections.<String>emptyList(), emptyHabitat().get(), rightConjunctZones, rightConjunctZones);
    SpiderDiagram spiderDiagram = createCompoundSD(Conjunction, leftConjunct, rightConjunct);
    new Combining().apply(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

  @Test(expected = TransformationException.class)
  public void apply_MUST_throw_an_exception_WHEN_a_spider_in_either_of_the_conjuncts_has_more_than_one_foot() throws RuleApplicationException {
    List<Zone> diagramZones = allZonesForContours("A", "B");
    Map<String, Region> multipleFeetHabitats = emptyHabitat().addHabitat("s", getZonesInsideAllContours(diagramZones, "A")).get();
    PrimarySpiderDiagram leftConjunct = createPrimarySD(asList("s"), multipleFeetHabitats, diagramZones, diagramZones);
    PrimarySpiderDiagram rightConjunct = createPrimarySD(asList("s"), multipleFeetHabitats, diagramZones, diagramZones);
    SpiderDiagram spiderDiagram = createCompoundSD(Conjunction, leftConjunct, rightConjunct);
    new Combining().apply(new SubDiagramIndexArg(0, 0), createGoalsFrom(spiderDiagram));
  }

}