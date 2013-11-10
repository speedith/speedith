package speedith.draw;

import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;
import speedith.core.reasoning.rules.transformers.CopyContoursTransformerTest;
import speedith.core.reasoning.util.unitary.ContourRelationsTest;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;
import speedith.core.reasoning.util.unitary.ZoneTransfer;
import speedith.core.reasoning.util.unitary.ZoneTransferTest;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static java.util.Arrays.asList;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.lang.Zones.*;
import static speedith.core.reasoning.rules.transformers.CopyContoursTransformerTest.diagramWithASpider;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;
import static speedith.draw.SpiderDiagramPanelTest.*;

public class DiagramTestPortfolio implements Serializable {
    public final PrimarySpiderDiagram shadedBInsideA = createPrimarySD(null, null, asList(CopyContoursTransformerTest.zoneBMinusA, CopyContoursTransformerTest.zoneBAndA), asList(CopyContoursTransformerTest.zoneBAndA, CopyContoursTransformerTest.zoneAMinusB));
    private ArrayList<SpiderDiagram> spiderDiagrams;

    public DiagramTestPortfolio() {
        this.spiderDiagrams = new ArrayList<>(asList(
                new ZoneTransfer(DIAGRAM_SPEEDITH_PAPER_FIG7_2, DIAGRAM_SPEEDITH_PAPER_FIG7_1).transferContour("D"),
                DIAGRAM_SPEEDITH_PAPER_FIG7_1,
                DIAGRAM_SPEEDITH_PAPER_FIG7_2,
                DIAGRAM_SPEEDITH_PAPER_FIG7_3,
                TestSpiderDiagrams.getDiagramSpeedithPaper_Fig2_D2("E", "A"),
                DIAGRAM_SPEEDITH_PAPER_FIG2_D1,
                DIAGRAM_SPEEDITH_PAPER_FIG2_D2,
                DIAGRAM_SPEEDITH_PAPER_FIG2_D1Prime,
                new ZoneTransfer(TestSpiderDiagrams.getDiagramSpeedithPaper_Fig2_D2("E", "A"), TestSpiderDiagrams.DIAGRAM_SPEEDITH_PAPER_FIG2_D1).transferContour("E"),
                new ZoneTransfer(TestSpiderDiagrams.getDiagramABCWhereCContainsA(), TestSpiderDiagrams.getVenn2Diagram("B", "C")).transferContour("A"),
                TestSpiderDiagrams.getDiagramABCWhereCContainsA(),
                TestSpiderDiagrams.getVenn2Diagram("B", "C"),
                new ZoneTransfer(TestSpiderDiagrams.getDiagramABCWhereCContainsA(), TestSpiderDiagrams.getVenn3Diagram("A", "B", "D")).transferContour("C"),
                ZoneTransferTest.diagramABC_shadedSetC_A,
                ZoneTransferTest.diagramABC_shadedSetAC,
                ContourRelationsTest.getVennABCDiagramWithPartlyShadedBAndSpiderInZoneBC_A(),
                ContourRelationsTest.getVennABCDiagramWithPartlyShadedB(),
                ContourRelationsTest.getVennABCDiagramWithShadedBC(),
                diagramWithASpider,
                shadedBInsideA,
                createPrimarySD(null, null, sameRegionWithNewContours(extendRegionWithNewContour(asList(Zone.fromInContours("A")), "B", null), "C"), POWER_REGION_ABC),
                createPrimarySD(null, null, sameRegionWithNewContours(asList(Zone.fromInContours("B")), "A", "C"), POWER_REGION_ABC),
                createPrimarySD(null, null, sameRegionWithNewContours(asList(Zone.fromInContours("B")), "A"), Zones.sameRegionWithNewContours(asList(Zone.fromInContours("B")), "A")),
                createPrimarySD(null, null, getZonesOutsideContours(POWER_REGION_ABCD, "C", "B"), POWER_REGION_ABCD),
                getSDExample1(),
                getSDExample2(),
                getSDExample3()
        ));
        loadFromTestFiles();
    }

    public List<SpiderDiagram> getSpiderDiagrams() {
        return Collections.unmodifiableList(spiderDiagrams);
    }

    public int size() {
        return getSpiderDiagrams().size();
    }

    public SpiderDiagram getDiagramAt(int spiderDiagramIndex) {
        return getSpiderDiagrams().get(spiderDiagramIndex);
    }

    public static void main(String[] args) {
        new LotsOfDiagramsForm().setVisible(true);
    }

    private void loadFromTestFiles() {
        for (int i = 0; i < TestSpiderDiagrams.getSpiderDiagramSDTFilesCount(); i++) {
            try {
                spiderDiagrams.add(TestSpiderDiagrams.readSpiderDiagramFromSDTFile(i));
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }
}