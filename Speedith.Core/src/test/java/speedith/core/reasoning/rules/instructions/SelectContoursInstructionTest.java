package speedith.core.reasoning.rules.instructions;

import org.junit.Test;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.selection.ContoursSelectionStep;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.beans.SamePropertyValuesAs.samePropertyValuesAs;
import static org.hamcrest.collection.IsIterableContainingInOrder.contains;
import static org.junit.Assert.assertThat;

public class SelectContoursInstructionTest {

    private SelectContoursInstruction selectContoursInstruction = new SelectContoursInstruction();

    @Test
    public void getSelectionSteps_should_return_a_single_contour_selection_step() {
        assertThat(
                selectContoursInstruction.getSelectionSteps(),
                contains(instanceOf(ContoursSelectionStep.class))
        );
    }

    @Test()
    public void extractRuleArg_should_return_multiple_contour_args_from_the_sequence() {
        MultipleRuleArgs ruleArgs = selectContoursInstruction.extractRuleArg(new TestContourSelectionSequence(new ContourArg(0, 3, "A")), 1);
        assertThat(
                ruleArgs.getRuleArgs(),
                contains(samePropertyValuesAs((RuleArg) new ContourArg(1, 3, "A")))
        );
    }
}
