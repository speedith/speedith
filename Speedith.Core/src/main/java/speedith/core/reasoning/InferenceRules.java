/*
 *   Project: Speedith.Core
 * 
 * File name: InferenceRules.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package speedith.core.reasoning;

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.rules.*;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * Contains a list of available {@link InferenceRule inference rules}, provides
 * detailed information about them (through their respective {@link
 * InferenceRuleProvider inference rule provider}) and acts as a means to
 * construct/fetch/instantiate inference rules for actual use in proofs.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class InferenceRules {

    public  static  final String diagram_type_preference = "diagram_type";

    /**
     * The map containing all currently registered inference rule providers.
     */
    private static final HashMap<String, InferenceRuleProvider<? extends RuleArg>> providers = new HashMap<>();

    static {
        // Register built-in inference rules.
        registerProvider(AddFeet.class);
        registerProvider(EraseSpider.class);
        registerProvider(IntroContour.class);
        registerProvider(RemoveContour.class);
        registerProvider(RemoveShading.class);
        registerProvider(IntroShadedZone.class);
        registerProvider(RemoveShadedZone.class);
        registerProvider(DischargeNullGoal.class);

        registerProvider(Combining.class);
        registerProvider(CopySpider.class);
        registerProvider(CopyContours.class);
        registerProvider(CopyContoursTopological.class);
        registerProvider(CopyShading.class);
        registerProvider(SplitSpiders.class);
        registerProvider(ExcludedMiddle.class);
        registerProvider(NegationElimination.class);

        registerProvider(ModusPonens.class);
        registerProvider(ModusTolens.class);
        registerProvider(Idempotency.class);
        registerProvider(IdempotencySyntactic.class);
        registerProvider(GeneralTautology.class);
        registerProvider(TrivialImplicationTautology.class);
        registerProvider(ImplicationTautology.class);
        registerProvider(ConjunctionElimination.class);
        registerProvider(SplitConjunction.class);
        registerProvider(SplitDisjunction.class);
        registerProvider(DisjunctionIntroduction.class);
        registerProvider(EquivalenceElimination.class);
        registerProvider(EquivalenceIntroduction.class);
        registerProvider(DoubleNegationElimination.class);
        registerProvider(DoubleNegationIntroduction.class);
    }

    /**
     * This is a 'static' class. No instantiation needed.
     */
    private InferenceRules() {
    }

    /**
     * The main method for fetching a Spider-diagrammatic {@link InferenceRule
     * inference rule}.
     * <p>You can get the inference rules by name.</p>
     * <p>This method throws an exception if the inference rule does not
     * exist.</p>
     * <p><span style="font-weight:bold">Note</span>: use {@link
     * InferenceRules#getProvider(java.lang.String)} to get more information
     * about the inference rule before fetching an actual one.</p>
     *
     * @param inferenceRule the name of the inference rule to fetch.
     * @return an {@link InferenceRule inference rule} that operates on spider
     *         diagrams.
     */
    public static InferenceRule<? extends RuleArg> getInferenceRule(String inferenceRule) {
        if (inferenceRule == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "inferenceRule"));
        }
        InferenceRuleProvider<? extends RuleArg> provider = providers.get(inferenceRule);
        return provider.getInferenceRule();
    }

    /**
     * Returns the {@link InferenceRuleProvider inference rule provider} of the
     * given name.
     * <p>Returns {@code null} if no such provider exists.</p>
     * <p><span style="font-weight:bold">Note</span>: the returned provider
     * contains a plethora of information about the inference rule (e.g.: how
     * the inference rule is used, what it does, and what arguments it
     * accepts).</p>
     *
     * @param inferenceRule the name of the inference rule for which to fetch
     *                      the provider.
     * @return the provider for the desired inference rule.
     *         <p>Returns {@code null} if no such provider exists.</p>
     */
    public static InferenceRuleProvider<? extends RuleArg> getProvider(String inferenceRule) {
        return providers.get(inferenceRule);
    }

    /**
     * Returns a set of names of all currently supported inference rules for the specified
     * diagram type..
     * <p>To get information about a particular inference rule, use the
     * {@link InferenceRules#getProvider(java.lang.String)} method.</p>
     * <p>Note: This method never returns {@code null}.</p>
     *
     * @param diagramType The {@link DiagramType diagram type} to which
     *                    the supported inference rules are applicable.
     *
     * @return a set of names of all currently supported inference rules.
     */
    public static Set<String> getKnownInferenceRules(DiagramType diagramType) {
        HashMap<String,InferenceRuleProvider<? extends RuleArg>> intermediate = new HashMap<>();
        for (Map.Entry<String, InferenceRuleProvider<? extends RuleArg> > entry : providers.entrySet()) {
            if(entry.getValue().getApplicableTypes().contains(diagramType)) {
                intermediate.put(entry.getKey(), entry.getValue());
            }
        }
        return Collections.unmodifiableSet(intermediate.keySet());
    }

    /**
     * Registers an instance of the given {@link InferenceRuleProvider} class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old inference rule providers that happen to
     * have the same name as the newly registered one.</p>
     *
     * @param providerClass the inference rule provider to register.
     */
    public static void registerProvider(Class<?> providerClass) {
        if (providerClass == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "providerClass"));
        }
        try {
            @SuppressWarnings("unchecked")
            InferenceRuleProvider<? extends RuleArg> theProvider = providerClass.asSubclass(InferenceRuleProvider.class).getConstructor().newInstance();
            synchronized (providers) {
                providers.put(theProvider.getInferenceName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }
}
