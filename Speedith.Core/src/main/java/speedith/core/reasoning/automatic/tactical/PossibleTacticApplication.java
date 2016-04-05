package speedith.core.reasoning.automatic.tactical;

import speedith.core.reasoning.Inference;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationType;
import speedith.core.reasoning.args.SubgoalIndexArg;
import speedith.core.reasoning.automatic.PossibleInferenceApplication;
import speedith.core.reasoning.tactical.TacticApplicationException;

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

    @Override
    public boolean apply(Proof p, String typeSpecifier) throws RuleApplicationException, TacticApplicationException {
        boolean applied = true;
        try {
            p.applyRule(getInference(), getArg(), RuleApplicationType.AUTOMATIC, typeSpecifier);
        } catch (Exception e) {
            applied = false;
        }
        return applied;
    }
}
