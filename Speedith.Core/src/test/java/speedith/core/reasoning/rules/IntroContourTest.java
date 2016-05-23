package speedith.core.reasoning.rules;

import org.junit.Before;
import org.junit.Test;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.TransformationException;
import speedith.core.lang.Zone;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectSingleSubDiagramAndContourInstruction;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.*;


/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
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

    @Test(expected = TransformationException.class)
    public void apply_should_throw_an_exception_when_introducing_a_contour_that_already_exists_in_the_unitary_diagram() throws RuleApplicationException {
        PrimarySpiderDiagram  targetDiagram = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;
        Goals targetOfInference = Goals.createGoalsFrom(targetDiagram);

        introContour.apply(new MultipleRuleArgs(new ContourArg(0, 0, "A")), targetOfInference);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_null() throws RuleApplicationException {
        introContour.apply(null, null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_not_of_the_right_type() throws RuleApplicationException {
        introContour.apply(new ZoneArg(0, 0, Zone.fromInContours("A")), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_sub_diagram_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentSpiderDiagrams = Arrays.asList(new ContourArg(0, 0, "A"), new ContourArg(0, 1, "B"));
        introContour.apply(new MultipleRuleArgs(contoursFromDifferentSpiderDiagrams), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_goal_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentGoals = Arrays.asList(new ContourArg(1, 0, "A"), new ContourArg(0, 0, "B"));
        introContour.apply(new MultipleRuleArgs(contoursFromDifferentGoals), null);
    }

    @Test
    public void getContourArgsFrom_should_return_a_list_of_contour_args() throws RuleApplicationException {
        List<ContourArg> expectedContourArgs = Arrays.asList(new ContourArg(0, 0, "A"), new ContourArg(0, 0, "B"));
        ArrayList<ContourArg> contourArgs = ContourArg.getContourArgsFrom(new MultipleRuleArgs(expectedContourArgs));
        assertEquals(expectedContourArgs, contourArgs);
    }

    @Test
    public void getInstructions_should_return_the_contours_and_subdiagram_selection_instructions() {
        assertThat(
                introContour.getInstructions(),
                instanceOf(SelectSingleSubDiagramAndContourInstruction.class)
        );
    }

    @Test
    public void apply_must_add_the_new_contour_to_in_and_out_sets_of_all_zones_euler_diagram()  throws RuleApplicationException {
        PrimarySpiderDiagram target = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;
        Goals targetOfInference = Goals.createGoalsFrom(target);
        SpiderDiagram expectedResult = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B_INTERSECT_C;

        RuleApplicationResult result = introContour.apply(new MultipleRuleArgs(new ContourArg(0,0,"C")), targetOfInference);

        assertThat(result.getGoals().getGoalAt(0),
                equalTo(expectedResult));

    }
}
