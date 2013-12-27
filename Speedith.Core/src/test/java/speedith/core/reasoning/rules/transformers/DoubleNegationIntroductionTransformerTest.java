package speedith.core.reasoning.rules.transformers;

import org.junit.Test;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createNullSD;

public class DoubleNegationIntroductionTransformerTest {

    @Test
    public void transforming_a_root_diagram_should_produce_a_doubly_negated_diagram() {
        DoubleNegationIntroductionTransformer transformer = new DoubleNegationIntroductionTransformer(0);

        SpiderDiagram transformedSpiderDiagram = createNullSD().transform(transformer, true);

        assertThat(
                transformedSpiderDiagram,
                equalTo(
                        doubleNegatedDiagram(createNullSD())
                )
        );
    }

    @Test
    public void transforming_a_nested_diagram_should_produce_a_nested_doubly_negated_diagram() {
        DoubleNegationIntroductionTransformer transformer = new DoubleNegationIntroductionTransformer(3);

        SpiderDiagram nestedSpiderDiagram = createNullSD();
        SpiderDiagram transformedSpiderDiagram = putDiagramIntoACompoundDiagram(nestedSpiderDiagram).transform(transformer, true);

        assertThat(
                transformedSpiderDiagram,
                equalTo(
                        putDiagramIntoACompoundDiagram(doubleNegatedDiagram(nestedSpiderDiagram))
                )
        );
    }

    public static SpiderDiagram doubleNegatedDiagram(SpiderDiagram nestedSpiderDiagram) {
        return createCompoundSD(Operator.Negation, createCompoundSD(Operator.Negation, nestedSpiderDiagram));
    }

    public static SpiderDiagram putDiagramIntoACompoundDiagram(SpiderDiagram nestedSpiderDiagram) {
        return createCompoundSD(Operator.Conjunction, createNullSD(), createCompoundSD(Operator.Implication, nestedSpiderDiagram, createNullSD()));
    }

}
