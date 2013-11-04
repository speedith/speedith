package speedith.core.reasoning.util.primary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.Zone;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.hasSize;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createPrimarySD;

public class ZoneTransferTest {

    private final PrimarySpiderDiagram diagramWithABZones = createPrimarySD(null, null, null, asList(Zone.fromInContours("A", "B")));
    private final PrimarySpiderDiagram diagramWithBCZones = createPrimarySD(null, null, null, asList(Zone.fromOutContours("B", "C")));

    @Test
    public void contoursOnlyInSource_returns_the_contour_that_is_present_in_the_source_diagram_but_not_in_the_destination_diagram() throws Exception {
        ZoneTransfer zoneTransfer = new ZoneTransfer(diagramWithABZones, diagramWithBCZones);
        assertThat(
                zoneTransfer.contoursOnlyInSource(),
                contains("A")
        );
    }

    @Test
    public void contoursOnlyInSource_returns_an_empty_set_when_the_source_diagram_has_no_contours() throws Exception {
        ZoneTransfer zoneTransfer = new ZoneTransfer(createPrimarySD(), diagramWithBCZones);
        assertThat(
                zoneTransfer.contoursOnlyInSource(),
                hasSize(0)
        );
    }
}
