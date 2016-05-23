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
import speedith.core.reasoning.rules.instructions.SelectContoursInstruction;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertThat;

/**
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class RemoveContourTest {

    private RemoveContour removeContour;

    @Before
    public void setUp() {
        removeContour = new RemoveContour();
    }

    @Test
    public void getInferenceRule_should_return_the_intro_contour_inference_rule() {
        assertSame(removeContour, removeContour.getInferenceRule());
    }

    @Test(expected = TransformationException.class)
    public void apply_should_throw_an_exception_when_removing_a_contour_that_does_not_exist_in_the_unitary_diagram() throws RuleApplicationException {
        PrimarySpiderDiagram targetDiagram = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;
        Goals targetOfInference = Goals.createGoalsFrom(targetDiagram);

        removeContour.apply(new MultipleRuleArgs(new ContourArg(0, 0, "C")), targetOfInference);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_null() throws RuleApplicationException {
        removeContour.apply(null, null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_not_of_the_right_type() throws RuleApplicationException {
        removeContour.apply(new ZoneArg(0, 0, Zone.fromInContours("A")), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_any_of_the_multiple_args_is_not_a_contour() throws RuleApplicationException {
        removeContour.apply(new MultipleRuleArgs(Arrays.asList(new ZoneArg(0, 0, Zone.fromInContours("A")))), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_sub_diagram_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentSpiderDiagrams = Arrays.asList(new ContourArg(0, 0, "A"), new ContourArg(0, 1, "B"));
        removeContour.apply(new MultipleRuleArgs(contoursFromDifferentSpiderDiagrams), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_goal_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentGoals = Arrays.asList(new ContourArg(1, 0, "A"), new ContourArg(0, 0, "B"));
        removeContour.apply(new MultipleRuleArgs(contoursFromDifferentGoals), null);
    }

    @Test
    public void getContourArgsFrom_should_return_a_list_of_contour_args() throws RuleApplicationException {
        List<ContourArg> expectedContourArgs = Arrays.asList(new ContourArg(0, 0, "A"), new ContourArg(0, 0, "B"));
        ArrayList<ContourArg> contourArgs = ContourArg.getContourArgsFrom(new MultipleRuleArgs(expectedContourArgs));
        assertEquals(expectedContourArgs, contourArgs);
    }

    @Test
    public void getInstructions_should_return_the_contours_selection_instructions() {
        assertThat(
                removeContour.getInstructions(),
                instanceOf(SelectContoursInstruction.class)
        );
    }

    @Test
    public void applyForwards_must_remove_the_contour_from_in_and_out_sets_of_all_zones_euler_diagram()  throws RuleApplicationException {
        PrimarySpiderDiagram target = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B_INTERSECT_C;
        Goals targetOfInference = Goals.createGoalsFrom(target);
        SpiderDiagram expectedResult = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;

        RuleApplicationResult result = removeContour.applyForwards(new MultipleRuleArgs(new ContourArg(0,0,"C")), targetOfInference);

        assertThat(result.getGoals().getGoalAt(0),
                equalTo(expectedResult));

    }

    @Test(expected = TransformationException.class)
    public void apply_should_throw_exception_when_not_in_fitting_position() throws RuleApplicationException {
        PrimarySpiderDiagram target = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B_INTERSECT_C;
        Goals targetOfInference = Goals.createGoalsFrom(target);


        RuleApplicationResult result = removeContour.apply(new MultipleRuleArgs(new ContourArg(0,0,"C")), targetOfInference);

    }
}
