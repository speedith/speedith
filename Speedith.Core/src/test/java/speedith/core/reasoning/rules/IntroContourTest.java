package speedith.core.reasoning.rules;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertSame;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 * Created by sl542 on 10/11/15.
 */
public class IntroContourTest {

    private IntroContour introContour;

    @Before
    public void setUp() {
        introContour = new IntroContour();
    }

    @Test
    public void getInferenceRule_should_return_the_intro_contour_inference_rule() {
        assertSame(introContour, introContour.getInferenceRule());
    }
}
