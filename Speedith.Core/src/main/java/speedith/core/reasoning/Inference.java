package speedith.core.reasoning;

import speedith.core.reasoning.args.RuleArg;

/**
 * The interface for every inference in Speedith. This could
 * be an {@link InferenceRule} or an {@link speedith.core.reasoning.tactical.InferenceTactic}.

 * @param <TArgs> the type of arguments the provided inference expects. Use
 * the type {@link RuleArg} to specify that the inference rule does not expect
 * any specific arguments.
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
