package speedith.core.reasoning.rules;

import org.junit.Before;
import org.junit.Test;
import speedith.core.lang.*;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectContoursInstruction;

import java.util.*;

import static org.hamcrest.CoreMatchers.*;
import static org.hamcrest.text.IsEmptyString.isEmptyOrNullString;
import static org.junit.Assert.*;
import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.*;

public class CopyContoursTest {

    private CopyContours copyContours;

    @Before
    public void setUp() throws Exception {
        copyContours = new CopyContours();
    }

    @Test
    public void getInferenceRule_should_return_the_copy_contours_inference_rule() {
        assertSame(copyContours, copyContours.getInferenceRule());
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_empty() throws RuleApplicationException {
        copyContours.apply(new MultipleRuleArgs(new ArrayList<ContourArg>()), null);
    }

    @Test(expected = TransformationException.class)
    public void apply_should_throw_an_exception_when_copying_a_contour_that_already_exists_in_the_other_unitary_diagram() throws RuleApplicationException {
        Set<Zone> present = new HashSet<>();
        present.add(Zone.fromOutContours("A"));
        PrimarySpiderDiagram leftAndRightUnitaryDiagram = SpiderDiagrams.createPrimarySD(null, null, null, present).addSpider("s", new Region(Zone.fromInContours("A")));
        CompoundSpiderDiagram conjunctiveCompoundDiagram = SpiderDiagrams.createCompoundSD(Operator.Conjunction, leftAndRightUnitaryDiagram, leftAndRightUnitaryDiagram);
        Goals targetOfInference = Goals.createGoalsFrom(conjunctiveCompoundDiagram);

        copyContours.apply(new MultipleRuleArgs(new ContourArg(0, 2, "A")), targetOfInference);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_null() throws RuleApplicationException {
        copyContours.apply(null, null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_not_of_the_right_type() throws RuleApplicationException {
        copyContours.apply(new ZoneArg(0, 0, Zone.fromInContours("A")), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_any_of_the_multiple_args_is_not_a_contour() throws RuleApplicationException {
        copyContours.apply(new MultipleRuleArgs(Arrays.asList(new ZoneArg(0, 0, Zone.fromInContours("A")))), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_sub_diagram_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentSpiderDiagrams = Arrays.asList(new ContourArg(0, 0, "A"), new ContourArg(0, 1, "B"));
        copyContours.apply(new MultipleRuleArgs(contoursFromDifferentSpiderDiagrams), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_contour_args_contain_different_goal_indices() throws RuleApplicationException {
        List<ContourArg> contoursFromDifferentGoals = Arrays.asList(new ContourArg(1, 0, "A"), new ContourArg(0, 0, "B"));
        copyContours.apply(new MultipleRuleArgs(contoursFromDifferentGoals), null);
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
                copyContours.getInstructions(),
                instanceOf(SelectContoursInstruction.class)
        );
    }

    @Test
    public void apply_on_the_speedith_D1_D2_example_should_return_D1Prime_D2() throws RuleApplicationException {
        SpiderDiagram conjunctiveCompoundDiagram = SpiderDiagrams.createCompoundSD(Operator.Conjunction, DIAGRAM_SPEEDITH_PAPER_FIG2_D2, DIAGRAM_SPEEDITH_PAPER_FIG2_D1);
        Goals targetOfInference = Goals.createGoalsFrom(conjunctiveCompoundDiagram);

        SpiderDiagram expectedGoal = SpiderDiagrams.createCompoundSD(Operator.Conjunction, DIAGRAM_SPEEDITH_PAPER_FIG2_D2, DIAGRAM_SPEEDITH_PAPER_FIG2_D1Prime);

        RuleApplicationResult applicationResult = copyContours.apply(new MultipleRuleArgs(new ContourArg(0, 1, "E")), targetOfInference);
        assertThat(
                applicationResult.getGoals().getGoalAt(0),
                equalTo(expectedGoal)
        );
    }

    @Test
    public void getArgumentType_should_return_the_multiple_args_class() {
        assertThat(
                copyContours.getArgumentType(),
                equalTo(MultipleRuleArgs.class)
        );
    }

    @Test
    public void user_facing_functions_should_return_some_strings() {
        assertThat(copyContours.getInferenceName(), not(isEmptyOrNullString()));
        assertThat(copyContours.getDescription(), not(isEmptyOrNullString()));
        assertThat(copyContours.getCategory(), not(isEmptyOrNullString()));
        assertThat(copyContours.getPrettyName(), not(isEmptyOrNullString()));
    }
}
