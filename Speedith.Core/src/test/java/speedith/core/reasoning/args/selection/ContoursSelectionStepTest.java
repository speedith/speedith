package speedith.core.reasoning.args.selection;

import org.junit.Test;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.rules.instructions.TestContourSelectionSequence;

import static org.junit.Assert.*;

public class ContoursSelectionStepTest {

    private final TestContourSelectionSequence singleContourSelectionSequence = new TestContourSelectionSequence(new ContourArg(0, 1, "A"));
    private ContoursSelectionStep contoursSelectionStep = new ContoursSelectionStep();

    @Test
    public void isFinished_should_return_false() {
        assertFalse(contoursSelectionStep.isFinished(singleContourSelectionSequence, 1));
    }

    @Test
    public void init_should_just_succeed() {
        assertNull(contoursSelectionStep.init(singleContourSelectionSequence, 1));
    }

    @Test
    public void isSkippable_should_say_no_if_no_selection_has_been_made_yet() {
        assertFalse(contoursSelectionStep.isSkippable(new TestContourSelectionSequence(), 0));
    }

    @Test
    public void isSkippable_should_say_yes_if_at_least_one_selection_has_been_made_yet() {
        assertTrue(contoursSelectionStep.isSkippable(singleContourSelectionSequence, 0));
    }
}
