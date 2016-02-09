package speedith.core.reasoning.rules.transformers;

import org.junit.Test;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.TransformationException;

import static org.hamcrest.Matchers.equalTo;
import static org.junit.Assert.assertThat;
import static speedith.core.lang.SpiderDiagrams.createCompoundSD;
import static speedith.core.lang.SpiderDiagrams.createNullSD;

public class DoubleNegationEliminationTransformerTest {

    @Test(expected = TransformationException.class)
    public void transform_should_throw_an_exception_when_target_diagram_not_doubly_negated() {
        DoubleNegationEliminationTransformer transformer = new DoubleNegationEliminationTransformer(0);
        createNullSD().transform(transformer);
    }

    @Test(expected = TransformationException.class)
    public void transform_should_throw_an_exception_when_target_diagram_only_singly_negated() {
        DoubleNegationEliminationTransformer transformer = new DoubleNegationEliminationTransformer(0);
        createCompoundSD(Operator.Negation, createNullSD()).transform(transformer);
    }

    @Test
    public void transform_should_return_the_null_diagram_if_it_is_doubly_negated() {
        SpiderDiagram nullSpiderDiagram = createNullSD();
        SpiderDiagram doublyNegatedNullDiagram = doubleNegate(nullSpiderDiagram);

        SpiderDiagram transformedDiagram = doublyNegatedNullDiagram.transform(new DoubleNegationEliminationTransformer(0));

        assertThat(
                transformedDiagram,
                equalTo(nullSpiderDiagram)
        );
    }

    @Test
    public void transform_should_return_the_null_diagram_if_it_is_doubly_negated_and_nested() {
        SpiderDiagram nullSpiderDiagram = createNullSD();
        SpiderDiagram doublyNegatedNullDiagram = putDiagramIntoACompoundDiagram(doubleNegate(nullSpiderDiagram));

        SpiderDiagram transformedDiagram = doublyNegatedNullDiagram.transform(new DoubleNegationEliminationTransformer(3));

        assertThat(
                transformedDiagram,
                equalTo(putDiagramIntoACompoundDiagram(nullSpiderDiagram))
        );
    }

    public static SpiderDiagram doubleNegate(SpiderDiagram nullSpiderDiagram) {
        return createCompoundSD(Operator.Negation, createCompoundSD(Operator.Negation, nullSpiderDiagram));
    }

    public static SpiderDiagram putDiagramIntoACompoundDiagram(SpiderDiagram nestedSpiderDiagram) {
        return createCompoundSD(Operator.Conjunction, createNullSD(), createCompoundSD(Operator.Implication, nestedSpiderDiagram, createNullSD()));
    }
}
