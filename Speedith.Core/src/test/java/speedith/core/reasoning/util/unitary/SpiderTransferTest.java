package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Region;
import speedith.core.lang.Zone;

import java.util.TreeMap;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class SpiderTransferTest {
    @Test(expected = IllegalArgumentException.class)
    public void transferSpider_should_throw_an_exception_if_the_spider_is_not_present_in_the_source_diagram() throws Exception {
        new SpiderTransfer(VENN_3_ABC_DIAGRAM, VENN_3_ABC_DIAGRAM).transferSpider("s");
    }

    @Test
    public void transferSpider_should_place_the_single_spider_in_a_venn_diagram_to_the_same_diagram_without_the_spider() throws Exception {
        String spider = "s";
        TreeMap<String, Region> habitats = new TreeMap<>();
        habitats.put(spider, new Region(Zone.fromInContours("A", "B", "C")));
        PrimarySpiderDiagram venn3AbcDiagramWithSpider = createPrimarySD(habitats.keySet(), habitats, null, VENN_3_ABC_DIAGRAM.getPresentZones());

        PrimarySpiderDiagram diagramWithTransferredSpider = new SpiderTransfer(venn3AbcDiagramWithSpider, VENN_3_ABC_DIAGRAM).transferSpider(spider);
        assertThat(
                diagramWithTransferredSpider,
                equalTo(venn3AbcDiagramWithSpider)
        );
    }

    @Test
    public void transferSpider_should_put_the_spider_into_the_corresponding_region_of_the_target_diagram() {
        PrimarySpiderDiagram targetDiagram = DIAGRAM_SPEEDITH_PAPER_FIG7_3;
        PrimarySpiderDiagram sourceDiagram = DIAGRAM_SPEEDITH_PAPER_FIG7_2;
        PrimarySpiderDiagram expectedDiagram = DIAGRAM_SPEEDITH_PAPER_FIG7_5;

        PrimarySpiderDiagram transformedDiagram = new SpiderTransfer(sourceDiagram, targetDiagram).transferSpider("s1");

        assertThat(
                transformedDiagram,
                equalTo(expectedDiagram)
        );
    }
}
