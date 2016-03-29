package speedith.core.reasoning.tactical;

import speedith.core.reasoning.Goals;
import speedith.core.reasoning.Inference;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface Tactic extends Inference<TacticApplicationResult> {

    @Override
    TacticApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException;
}
