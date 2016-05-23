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
import speedith.core.reasoning.rules.instructions.SelectSingleZoneInstruction;
import speedith.core.reasoning.util.unitary.TestSpiderDiagrams;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertThat;

/**
 * Tests for the "Remove shaded zone" rule
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class RemoveShadedZoneTest {


    private RemoveShadedZone removeShadedZone;

    @Before
    public void setUp() {
        removeShadedZone = new RemoveShadedZone();
    }

    @Test
    public void getInferenceRule_should_return_the_remove_shaded_zone_inference_rule() {
        assertSame(removeShadedZone, removeShadedZone.getInferenceRule());
    }

    @Test(expected = TransformationException.class)
    public void apply_should_throw_an_exception_when_removing_a_zone_that_is_missing_in_the_unitary_diagram() throws RuleApplicationException {
        PrimarySpiderDiagram targetDiagram = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;
        Goals targetOfInference = Goals.createGoalsFrom(targetDiagram);

        removeShadedZone.apply(new MultipleRuleArgs(new ZoneArg(0, 0, new Zone(Collections.singleton("A"),Collections.singleton("B")))), targetOfInference);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_null() throws RuleApplicationException {
        removeShadedZone.apply(null, null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_the_arguments_are_not_of_the_right_type() throws RuleApplicationException {
        removeShadedZone.apply(new ContourArg(0, 0, "A"), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_zone_args_contain_different_sub_diagram_indices() throws RuleApplicationException {
        List<ZoneArg> zonesFromDifferentSpiderDiagrams = Arrays.asList(new ZoneArg(0, 0, Zone.fromInContours("A")), new ZoneArg(0, 1, Zone.fromInContours("B")));
        removeShadedZone.apply(new MultipleRuleArgs(zonesFromDifferentSpiderDiagrams), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_zone_args_contain_different_goal_indices() throws RuleApplicationException {
        List<ZoneArg> zonesFromDifferentGoals = Arrays.asList(new ZoneArg(1, 0, Zone.fromInContours("A")), new ZoneArg(0, 0, Zone.fromInContours("B")));
        removeShadedZone.apply(new MultipleRuleArgs(zonesFromDifferentGoals), null);
    }

    @Test(expected = RuleApplicationException.class)
    public void apply_should_throw_an_exception_when_zone_args_refers_to_outer_zone() throws RuleApplicationException {
        PrimarySpiderDiagram target = TestSpiderDiagrams.VENN_DIAGRAM_EVERYTHING_A_OR_B;
        Goals targetOfInference = Goals.createGoalsFrom(target);
        RuleApplicationResult result = removeShadedZone.apply(new MultipleRuleArgs(new ZoneArg(0,0,Zone.fromOutContours("A","B"))), targetOfInference);
    }


    @Test
    public void getZoneArgsFrom_should_return_a_list_of_zone_args() throws RuleApplicationException {
        List<ZoneArg> expectedZoneArgs = Arrays.asList(new ZoneArg(0, 0, Zone.fromInContours("A")), new ZoneArg(0, 0, Zone.fromInContours("B")));
        List<ZoneArg> zoneArgsFrom = ZoneArg.getZoneArgsFrom(new MultipleRuleArgs(expectedZoneArgs));
        assertEquals(expectedZoneArgs, zoneArgsFrom);
    }

    @Test
    public void getInstructions_should_return_single_zone_selection_instruction() {
        assertThat(
        removeShadedZone.getInstructions(),
                instanceOf(SelectSingleZoneInstruction.class));
    }

    @Test
    public void apply_must_remove_the_zone_from_set_of_present_zones_of_euler_diagram()  throws RuleApplicationException {
        PrimarySpiderDiagram target = TestSpiderDiagrams.VENN_DIAGRAM_A_SUBSET_B;
        Goals targetOfInference = Goals.createGoalsFrom(target);
        SpiderDiagram expectedResult = TestSpiderDiagrams.EULER_DIAGRAM_A_SUBSET_B;
        Zone introduce = new Zone(Collections.singleton("A"),Collections.singleton("B"));

        RuleApplicationResult result = removeShadedZone.apply(new MultipleRuleArgs(new ZoneArg(0,0,introduce)), targetOfInference);

        assertThat(result.getGoals().getGoalAt(0),
                equalTo(expectedResult));

    }
}
