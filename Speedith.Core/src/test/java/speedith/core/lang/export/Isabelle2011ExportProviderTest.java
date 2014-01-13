package speedith.core.lang.export;

import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.AddFeet;
import speedith.core.reasoning.rules.Idempotency;
import speedith.core.reasoning.rules.ImplicationTautology;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createNullSD;
import static speedith.core.reasoning.Goals.createGoalsFrom;

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

    private SpiderDiagram assertFig1InitialGoal() throws ExportException {
        SpiderDiagram diagram1 = TestSpiderDiagrams.tryReadSpiderDiagramFromSDTFile(0);
        String expectedIsaFormula1 = "(EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : (A - B) Un (B - A)) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))";
        assertFormulaEquals(expectedIsaFormula1, isabelleExporter.export(diagram1));
        return diagram1;
    }

    private SpiderDiagram assertFig1_Steps2_to_6_AddFoot(SpiderDiagram diagram, int subDiagramIndex, String spider, Zone zoneOfNewFoot, String exptecedIsaFormula) throws RuleApplicationException, ExportException {
        return assertInferenceStep(AddFeet.InferenceRuleName, new SpiderRegionArg(0, subDiagramIndex, spider, new Region(zoneOfNewFoot)), diagram, exptecedIsaFormula);
    }

    private SpiderDiagram assertInferenceStep(String inferenceRuleName, RuleArg ruleArg, SpiderDiagram diagram, String exptecedIsaFormula) throws RuleApplicationException, ExportException {
        SpiderDiagram diagramWithNewFoot = applyRule(inferenceRuleName, diagram, ruleArg);
        assertFormulaEquals(exptecedIsaFormula, isabelleExporter.export(diagramWithNewFoot));
        return diagramWithNewFoot;
    }

    private SpiderDiagram assertFig1Step1_SplitSpider(SpiderDiagram diagram) throws RuleApplicationException, ExportException {
        SpiderRegionArg regionOfSplit = new SpiderRegionArg(0, 1, "s2", new Region(zone_A_B));
        SpiderDiagram diagram2 = applyRule(SplitSpiders.InferenceRuleName, diagram, regionOfSplit);
        String expectedIsaFormula2 = "(EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : A - B) | (EX s1 s2. distinct[s1, s2] & s1 : A Int B & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))";
        assertFormulaEquals(expectedIsaFormula2, isabelleExporter.export(diagram2));
        return diagram2;
    }

    private SpiderDiagram applyRule(String inferenceRuleName, SpiderDiagram inferenceTarget, RuleArg ruleArguments) throws RuleApplicationException {
        return InferenceRules.getInferenceRule(inferenceRuleName).apply(ruleArguments, createGoalsFrom(inferenceTarget)).getGoals().getGoalAt(0);
    }

    private void assertFormulaEquals(String expectedIsaFormula, String isaFormula) {
        assertThat(
                isaFormula,
                equalTo(expectedIsaFormula)
        );
    }
}
