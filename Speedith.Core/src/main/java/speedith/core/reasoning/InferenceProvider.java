package speedith.core.reasoning;

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.args.RuleArg;

import java.util.Locale;
import java.util.Set;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface InferenceProvider<TArgs extends RuleArg> {

    /**
     * Returns the description of the provided inference rule. <p>By default,
     * this method should call the {@link
     * InferenceRuleProvider#getDescription(java.util.Locale)} method with the
     * {@link Locale#getDefault() default locale}.</p>
     *
     * @return the description of the provided inference rule.
     */
    String getDescription();

    /**
     * Returns the description of the provided inference rule in the given
     * {@link Locale locale}.
     *
     * @param locale the locale in which to give the description.
     * @return the description of the provided inference rule in the given
     * {@link Locale locale}.
     */
    String getDescription(Locale locale);

    /**
     * Returns a pretty human-readable short name of the provided inference
     * rule. <p>The name should not be more than half a dozen words in length as
     * it will be displayed in a drop-down list to the user.</p> <p>By default,
     * this method should call the {@link
     * InferenceRuleProvider#getPrettyName(java.util.Locale)} method with the
     * {@link Locale#getDefault() default locale}.</p>
     *
     * @return a pretty human-readable short name of the provided inference
     * rule.
     */
    String getPrettyName();

    /**
     * Returns a pretty human-readable short name of the provided inference
     * rule. <p>The name should not be more than half a dozen words in length as
     * it will be displayed in a drop-down list to the user.</p>
     *
     * @param locale the locale to which to translate the returned string.
     * @return a pretty human-readable short name of the provided inference
     * rule.
     */
    String getPrettyName(Locale locale);

    /**
     * Returns the type of the argument the provided inference rule requires.
     * The argument of this type is required in the inference rules' {@link
     * InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * apply method}. <p>Also, see the {@link InferenceRuleProvider#getDescription()
     * description} for more information on how to use the inference rule.</p>
     *
     * @return the type of the argument the provided inference rule requires.
     */
    Class<TArgs> getArgumentType();

    /**
     * Returns the set of all {@link DiagramType diagram types} the provided rule
     * is applicable to.
     *
     * @return the {@link Set} of {@link DiagramType diagram types} the rule provided
     * by this provider is applicable to
     */
    Set<DiagramType> getApplicableTypes();

    /**
     * Returns the name of the {@link InferenceRule} this provider provides.
     * <p><span style="font-weight:bold">Note</span>: this name is not
     * internationalised.</p>
     *
     * @return the name of the {@link InferenceRule} this provider provides.
     */
    String getInferenceName();



}
