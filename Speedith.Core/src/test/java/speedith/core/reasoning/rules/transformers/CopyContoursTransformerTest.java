package speedith.core.reasoning.rules.transformers;

import org.junit.Before;
import org.junit.Test;
import speedith.core.lang.*;

import static org.junit.Assert.assertEquals;

public class CopyContoursTransformerTest {
    @Before
    public void setUp() throws Exception {
    }

    @Test
    public void should_not_transform_the_diagram_if_they_share_the_same_contour() {
        CopyContoursTransformer copyContoursTransformer = new CopyContoursTransformer();
        PrimarySpiderDiagram leftAndRightUnitaryDiagram = SpiderDiagrams.createPrimarySD()
                                                                        .addSpider("s", new Region(Zone.fromInContours("A")));
        CompoundSpiderDiagram conjunctiveCompoundDiagram = SpiderDiagrams.createCompoundSD(Operator.Conjunction, leftAndRightUnitaryDiagram, leftAndRightUnitaryDiagram);

        assertEquals(conjunctiveCompoundDiagram, conjunctiveCompoundDiagram.transform(copyContoursTransformer, true));
    }
}
