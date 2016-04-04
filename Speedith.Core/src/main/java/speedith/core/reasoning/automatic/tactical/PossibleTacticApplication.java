package speedith.core.reasoning.automatic.tactical;

import speedith.core.reasoning.Inference;
import speedith.core.reasoning.args.SubgoalIndexArg;
import speedith.core.reasoning.automatic.PossibleInferenceApplication;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleTacticApplication extends PossibleInferenceApplication<SubgoalIndexArg> {

    public PossibleTacticApplication(int subGoalIndex, Inference<SubgoalIndexArg, ?> inference) {
        super(subGoalIndex, inference);
    }

    @Override
    public SubgoalIndexArg getArg() {
        return new SubgoalIndexArg(getSubGoalIndex());
    }
}
