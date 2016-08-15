package speedith.core.reasoning.tactical;

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.args.RuleArg;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * Hosts the difference Tactics that are available within Speedith. A new
 * tactic has to be registered in this class to be presented in the UI.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class Tactics {

    public static String level_preference = "level";

    /**
     * The map containing all currently registered tactic providers.
     */
    private static final HashMap<String, TacticProvider> providers = new HashMap<>();

    static {
        registerProvider(UnifyContours.class);
        registerProvider(UnifyContoursFocused.class);
        registerProvider(CopyTopologicalInformation.class);
        registerProvider(MatchConclusion.class);
        registerProvider(Venn.class);
        registerProvider(CopyShadingInformation.class);
        registerProvider(CopyEverything.class);
        registerProvider(VennFocused.class);
        registerProvider(Vennify.class);
        registerProvider(VennifyFocused.class);
        registerProvider(CombineAll.class);
        registerProvider(PrepareCopyContours.class);
        registerProvider(PrepareCopyShading.class);
        registerProvider(DeVennify.class);
        registerProvider(AutoCopy.class);
        registerProvider(AutoVenn.class);

    }

    private Tactics() {}
    /**
     * The main method for fetching a Spider-diagrammatic {@link InferenceTactic
     * tactic}.
     * <p>You can get the tactics by name.</p>
     * <p>This method throws an exception if the inference rule does not
     * exist.</p>
     * <p><span style="font-weight:bold">Note</span>: use {@link
     * Tactics#getProvider(java.lang.String)} to get more information
     * about the inference rule before fetching an actual one.</p>
     *
     * @param tactic the name of the inference rule to fetch.
     * @return an {@link InferenceTactic inference rule} that operates on spider
     *         diagrams.
     */
    public static InferenceTactic<? extends RuleArg> getTactic(String tactic) {
        if (tactic == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "inferenceRule"));
        }
        TacticProvider  provider = providers.get(tactic);
        return provider.getTactic();
    }

    /**
     * Returns the {@link TacticProvider tactic provider} of the
     * given name.
     * <p>Returns {@code null} if no such provider exists.</p>
     * <p><span style="font-weight:bold">Note</span>: the returned provider
     * contains a plethora of information about the inference rule (e.g.: how
     * the inference rule is used, what it does, and what arguments it
     * accepts).</p>
     *
     * @param tactic the name of the inference rule for which to fetch
     *                      the provider.
     * @return the provider for the desired inference rule.
     *         <p>Returns {@code null} if no such provider exists.</p>
     */
    public static TacticProvider getProvider(String tactic) {
        return providers.get(tactic);
    }

    /**
     * Registers an instance of the given {@link TacticProvider} class.
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
            TacticProvider theProvider = providerClass.asSubclass(TacticProvider.class).getConstructor().newInstance();
            synchronized (providers) {
                providers.put(theProvider.getInferenceName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }

    /**
     * Returns a set of names of all currently supported inference rules for the specified
     * diagram type..
     * <p>To get information about a particular inference rule, use the
     * {@link Tactics#getProvider(java.lang.String)} method.</p>
     * <p>Note: This method never returns {@code null}.</p>
     *
     * @param diagramType The {@link DiagramType diagram type} to which
     *                    the supported inference rules are applicable.
     *
     * @return a set of names of all currently supported inference rules.
     */
    public static Set<String> getKnownTactics(DiagramType diagramType, Boolean includingLowLevel) {
        HashMap<String,TacticProvider> intermediate = new HashMap<>();
        if (includingLowLevel) {
            for (Map.Entry<String, TacticProvider> entry : providers.entrySet()) {
                if (entry.getValue().getApplicableTypes().contains(diagramType)) {
                    intermediate.put(entry.getKey(), entry.getValue());
                }
            }
        } else {
            // only show high level rules
            for (Map.Entry<String, TacticProvider> entry : providers.entrySet()) {
                if (entry.getValue().isHighLevel() && entry.getValue().getApplicableTypes().contains(diagramType)) {
                    intermediate.put(entry.getKey(), entry.getValue());
                }
            }
        }
        return Collections.unmodifiableSet(intermediate.keySet());
    }

}
