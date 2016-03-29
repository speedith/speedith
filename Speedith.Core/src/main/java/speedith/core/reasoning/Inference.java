package speedith.core.reasoning;

import speedith.core.reasoning.args.RuleArg;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface Inference<TResult extends InferenceApplicationResult> {

    TResult apply(RuleArg args, Goals goals) throws RuleApplicationException;
}
