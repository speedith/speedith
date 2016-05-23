package speedith.core.lang.export;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.InferenceRuleProvider;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.*;
import speedith.core.reasoning.rules.*;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.util.ArrayList;
import java.util.List;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createNullSD;
import static speedith.core.reasoning.Goals.createGoalsFrom;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.diagramSpeedithPaperFig7Goal;

public class Isabelle2011ExportProviderTest {

    public final SDExporter isabelleExporter = SDExporting.getExporter(Isabelle2011ExportProvider.FormatName);
    public final Zone zone_A_B = Zone.fromInContours("A").withOutContours("B");
    public final Zone zone_AB = Zone.fromInContours("A", "B");
    public final Zone zone_B_A = Zone.fromInContours("B").withOutContours("A");

    @Test
    public void exporting_a_null_spider_diagram_must_produce_True() throws ExportException {
        String isabelleFormula = isabelleExporter.export(createNullSD());
        assertFormulaEquals("True", isabelleFormula);
    }

    @Test
    public void exporting_a_compound_spider_diagram_of_null_diagrams() throws ExportException {
        String isabelleFormula = isabelleExporter.export(createCompoundSD(Operator.Implication, createNullSD(), createNullSD()));
        assertFormulaEquals("True --> True", isabelleFormula);
    }

    @Test
    public void bug_exporting_speedith_paper_fig7_2_diagram() throws ExportException {
        PrimarySpiderDiagram spiderDiagram = TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG7_2;
        String isabelleFormula = isabelleExporter.export(spiderDiagram);
        assertFormulaEquals("(EX s1 s2. distinct[s1, s2] & s1 : -(C Un D) & s2 : (C - D) Un (C Int D) & C - D <= {s1, s2} & D - C <= {s1, s2})", isabelleFormula);
    }

    @Test
    public void speedith_paper_fig1_proof() throws ExportException, RuleApplicationException {
        SpiderDiagram diagram1 = assertFig1InitialGoal();
        SpiderDiagram diagram2 = assertFig1Step1_SplitSpider(diagram1);
        SpiderDiagram diagram3 = assertFig1_Steps2_to_6_AddFoot(diagram2, 2, "s2", zone_AB, "(EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : (A - B) Un (A Int B)) | (EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))");
        SpiderDiagram diagram4 = assertFig1_Steps2_to_6_AddFoot(diagram3, 2, "s1", zone_B_A, "(EX s1 s2. distinct[s1, s2] & s1 : (A Int B) Un (B - A) & s2 : (A - B) Un (A Int B)) | (EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))");
        SpiderDiagram diagram5 = assertFig1_Steps2_to_6_AddFoot(diagram4, 3, "s1", zone_A_B, "(EX s1 s2. distinct[s1, s2] & s1 : (A Int B) Un (B - A) & s2 : (A - B) Un (A Int B)) | (EX s1 s2. distinct[s1, s2] & s1 : (A - B) Un (A Int B) & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))");
        SpiderDiagram diagram6 = assertFig1_Steps2_to_6_AddFoot(diagram5, 3, "s2", zone_AB, "(EX s1 s2. distinct[s1, s2] & s1 : (A Int B) Un (B - A) & s2 : (A - B) Un (A Int B)) | (EX s1 s2. distinct[s1, s2] & s1 : (A - B) Un (A Int B) & s2 : (A Int B) Un (B - A)) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))");
        SpiderDiagram diagram7 = assertInferenceStep(Idempotency.InferenceRuleName, new SubDiagramIndexArg(0, 1), diagram6, "(EX s1 s2. distinct[s1, s2] & s1 : (A - B) Un (A Int B) & s2 : (A Int B) Un (B - A)) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))");
        assertInferenceStep(ImplicationTautology.InferenceRuleName, new SubDiagramIndexArg(0, 0), diagram7, "True");
    }

    @Test
    public void speedith_paper_fig7_proof() throws ExportException, RuleApplicationException {
        SpiderDiagram initialGoal = assertFig7InitialGoal();
        SpiderDiagram subgoal1 = assertInferenceStep(new CopyContours(), new MultipleRuleArgs(new ContourArg(0, 3, "D")), initialGoal, "(EX s. s : (C - (A Un B Un D)) Un ((C Int D) - (A Un B)) & (A Int B Int C) - D <= {s} & A Int B Int C Int D <= {s} & (A Int B Int D) - C <= {s} & (A Int C) - (B Un D) <= {s} & (A Int C Int D) - B <= {s} & (A Int D) - (B Un C) <= {s} & B - (A Un C Un D) <= {s} & (B Int C) - (A Un D) <= {s} & (B Int C Int D) - A <= {s} & (B Int D) - (A Un C) <= {s} & D - (A Un B Un C) <= {s}) & (EX s1 s2. distinct[s1, s2] & s1 : -(C Un D) & s2 : (C - D) Un (C Int D) & C - D <= {s1, s2} & D - C <= {s1, s2}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})");
        SpiderDiagram subgoal2 = assertInferenceStep(new CopySpider(), new SpiderArg(0, 3, "s1"), subgoal1, "(EX s s1. distinct[s, s1] & s : (C - (A Un B Un D)) Un ((C Int D) - (A Un B)) & s1 : (-(A Un B Un C Un D)) Un (A - (B Un C Un D)) Un ((A Int B) - (C Un D)) & (A Int B Int C) - D <= {s, s1} & A Int B Int C Int D <= {s, s1} & (A Int B Int D) - C <= {s, s1} & (A Int C) - (B Un D) <= {s, s1} & (A Int C Int D) - B <= {s, s1} & (A Int D) - (B Un C) <= {s, s1} & B - (A Un C Un D) <= {s, s1} & (B Int C) - (A Un D) <= {s, s1} & (B Int C Int D) - A <= {s, s1} & (B Int D) - (A Un C) <= {s, s1} & D - (A Un B Un C) <= {s, s1}) & (EX s1 s2. distinct[s1, s2] & s1 : -(C Un D) & s2 : (C - D) Un (C Int D) & C - D <= {s1, s2} & D - C <= {s1, s2}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})");
        SpiderDiagram subgoal3 = assertInferenceStep(new CopyShading(), new MultipleRuleArgs(new ZoneArg(0, 3, Zone.fromInContours("C").withOutContours("D"))), subgoal2, "(EX s s1. distinct[s, s1] & s : (C - (A Un B Un D)) Un ((C Int D) - (A Un B)) & s1 : (-(A Un B Un C Un D)) Un (A - (B Un C Un D)) Un ((A Int B) - (C Un D)) & (A Int B Int C) - D <= {s, s1} & A Int B Int C Int D <= {s, s1} & (A Int B Int D) - C <= {s, s1} & (A Int C) - (B Un D) <= {s, s1} & (A Int C Int D) - B <= {s, s1} & (A Int D) - (B Un C) <= {s, s1} & B - (A Un C Un D) <= {s, s1} & (B Int C) - (A Un D) <= {s, s1} & (B Int C Int D) - A <= {s, s1} & (B Int D) - (A Un C) <= {s, s1} & C - (A Un B Un D) <= {s, s1} & D - (A Un B Un C) <= {s, s1}) & (EX s1 s2. distinct[s1, s2] & s1 : -(C Un D) & s2 : (C - D) Un (C Int D) & C - D <= {s1, s2} & D - C <= {s1, s2}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})");
        SubDiagramIndexArg compound = new SubDiagramIndexArg(0, 1);
        SubDiagramIndexArg target = new SubDiagramIndexArg(0,2);
        List<SubDiagramIndexArg> l = new ArrayList<>();
        l.add(compound);
        l.add(target);
        SpiderDiagram subgoal4 = assertInferenceStep(new ConjunctionElimination(), new MultipleRuleArgs(l), subgoal3, "(EX s s1. distinct[s, s1] & s : (C - (A Un B Un D)) Un ((C Int D) - (A Un B)) & s1 : (-(A Un B Un C Un D)) Un (A - (B Un C Un D)) Un ((A Int B) - (C Un D)) & (A Int B Int C) - D <= {s, s1} & A Int B Int C Int D <= {s, s1} & (A Int B Int D) - C <= {s, s1} & (A Int C) - (B Un D) <= {s, s1} & (A Int C Int D) - B <= {s, s1} & (A Int D) - (B Un C) <= {s, s1} & B - (A Un C Un D) <= {s, s1} & (B Int C) - (A Un D) <= {s, s1} & (B Int C Int D) - A <= {s, s1} & (B Int D) - (A Un C) <= {s, s1} & C - (A Un B Un D) <= {s, s1} & D - (A Un B Un C) <= {s, s1}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})");
        assertInferenceStep(new RemoveContour(), new MultipleRuleArgs(new ContourArg(0, 1, "A"), new ContourArg(0, 1, "C")), subgoal4, "(EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})");
    }

    private SpiderDiagram assertFig7InitialGoal() throws ExportException {
        SpiderDiagram initialGoal = diagramSpeedithPaperFig7Goal();
        String expectedIsaFormula = "(EX s. s : C - (A Un B) & A Int B Int C <= {s} & (A Int C) - B <= {s} & B - (A Un C) <= {s} & (B Int C) - A <= {s}) & (EX s1 s2. distinct[s1, s2] & s1 : -(C Un D) & s2 : (C - D) Un (C Int D) & C - D <= {s1, s2} & D - C <= {s1, s2}) --> (EX s s1. distinct[s, s1] & s : (-(B Un D)) Un (D - B) & s1 : (-(B Un D)) Un (B - D) & B Int D <= {s, s1})";
        assertExport(initialGoal, expectedIsaFormula);
        return initialGoal;
    }

    private SpiderDiagram assertFig1InitialGoal() throws ExportException {
        SpiderDiagram diagram1 = TestSpiderDiagrams.tryReadSpiderDiagramFromSDTFile(0);
        String expectedIsaFormula1 = "(EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : (A - B) Un (B - A)) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))";
        return assertExport(diagram1, expectedIsaFormula1);
    }

    private SpiderDiagram assertExport(SpiderDiagram diagram, String expectedIsaFormula) throws ExportException {
        assertFormulaEquals(expectedIsaFormula, isabelleExporter.export(diagram));
        return diagram;
    }

    private SpiderDiagram assertFig1_Steps2_to_6_AddFoot(SpiderDiagram diagram, int subDiagramIndex, String spider, Zone zoneOfNewFoot, String expectedIsaFormula) throws RuleApplicationException, ExportException {
        return assertInferenceStep(AddFeet.InferenceRuleName, new SpiderRegionArg(0, subDiagramIndex, spider, new Region(zoneOfNewFoot)), diagram, expectedIsaFormula);
    }

    private SpiderDiagram assertFig1Step1_SplitSpider(SpiderDiagram diagram) throws RuleApplicationException, ExportException {
        SpiderRegionArg regionOfSplit = new SpiderRegionArg(0, 1, "s2", new Region(zone_A_B));
        SpiderDiagram diagram2 = applyRule(SplitSpiders.InferenceRuleName, diagram, regionOfSplit);
        String expectedIsaFormula2 = "(EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : A - B) | (EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))";
        return assertExport(diagram2, expectedIsaFormula2);
    }

    private SpiderDiagram applyRule(String inferenceRuleName, SpiderDiagram inferenceTarget, RuleArg ruleArguments) throws RuleApplicationException {
        return InferenceRules.getInferenceRule(inferenceRuleName).apply(ruleArguments, createGoalsFrom(inferenceTarget)).getGoals().getGoalAt(0);
    }

    private SpiderDiagram assertInferenceStep(String inferenceRuleName, RuleArg ruleArg, SpiderDiagram diagram, String expectedIsaFormula) throws RuleApplicationException, ExportException {
        SpiderDiagram diagramWithNewFoot = applyRule(inferenceRuleName, diagram, ruleArg);
        return assertExport(diagramWithNewFoot, expectedIsaFormula);
    }

    private <T extends RuleArg> SpiderDiagram assertInferenceStep(InferenceRuleProvider<T> inferenceRule, T ruleArg, SpiderDiagram diagram, String expectedIsaFormula) throws RuleApplicationException, ExportException {
        return assertInferenceStep(inferenceRule.getInferenceName(), ruleArg, diagram, expectedIsaFormula);
    }

    private void assertFormulaEquals(String expectedIsaFormula, String isaFormula) {
        assertThat(
                isaFormula,
                equalTo(expectedIsaFormula)
        );
    }
}
