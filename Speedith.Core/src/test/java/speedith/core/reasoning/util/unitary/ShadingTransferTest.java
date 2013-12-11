package speedith.core.reasoning.util.unitary;

import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.TransformationException;
import speedith.core.lang.Zone;

import static java.util.Arrays.asList;
import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class ShadingTransferTest {

    @Test(expected = TransformationException.class)
    public void transferShading_should_throw_an_exception_if_the_zone_is_not_shaded_in_source_diagram() {
        ShadingTransfer shadingTransfer = new ShadingTransfer(DIAGRAM_SPEEDITH_PAPER_FIG7_1, DIAGRAM_SPEEDITH_PAPER_FIG7_2);
        shadingTransfer.transferShading(asList(Zone.fromInContours("A", "B").withOutContours("C")));
    }

    @Test()
    public void transferShading_should_make_the_re() {
        Zone newShadedZone = Zone.fromInContours("C").withOutContours("D");
        ShadingTransfer shadingTransfer = new ShadingTransfer(
                DIAGRAM_SPEEDITH_PAPER_FIG7_2,
                DIAGRAM_SPEEDITH_PAPER_FIG7_3
        );

        PrimarySpiderDiagram resultDiagram = shadingTransfer.transferShading(asList(newShadedZone));

        assertThat(
                resultDiagram,
                equalTo(DIAGRAM_SPEEDITH_PAPER_FIG7_3_SHADED_C)
        );
    }
}
