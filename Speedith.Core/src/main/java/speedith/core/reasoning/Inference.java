package speedith.core.reasoning;

import speedith.core.reasoning.args.RuleArg;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface Inference<TArgs extends RuleArg, TResult extends InferenceApplicationResult> {

    TResult apply(RuleArg args, Goals goals) throws RuleApplicationException;


    /**
     * Returns the provider of this rule. This provider gives all the
     * meta-information about this rule (human-readable description, formal
     * properties of the rule like equivalence preserving etc.). <p><span
     * style="font-weight:bold">Note:</span> the return value of this
     * function</p> must not be {@code null}.
     *
     * @return the provider of this rule.
     */
    InferenceProvider<TArgs> getProvider();

}
