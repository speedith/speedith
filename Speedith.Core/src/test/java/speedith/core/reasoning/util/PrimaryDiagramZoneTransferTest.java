package speedith.core.reasoning.util;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.Zone;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.contains;
import static org.junit.Assert.assertThat;

public class PrimaryDiagramZoneTransferTest {

    private final PrimarySpiderDiagram diagramWithABZones = SpiderDiagrams.createPrimarySD(null, null, null, asList(Zone.fromInContours("A", "B")));
    private final PrimarySpiderDiagram diagramWithBCZones = SpiderDiagrams.createPrimarySD(null, null, null, asList(Zone.fromOutContours("B", "C")));

    @Test
    public void testMissingContoursInTarget() throws Exception {
        PrimaryDiagramZoneTransfer zoneTransfer = new PrimaryDiagramZoneTransfer(diagramWithABZones, diagramWithBCZones);
        assertThat(
                zoneTransfer.missingContoursInTarget(),
                contains("A")
        );
    }
}
