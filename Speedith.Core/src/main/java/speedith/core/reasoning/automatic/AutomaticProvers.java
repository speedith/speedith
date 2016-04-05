package speedith.core.reasoning.automatic;

import java.util.Collections;
import java.util.HashMap;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AutomaticProvers {

    public static final String prover_preference = "automatic";

    private static final HashMap<String, AutomaticProverProvider> providers = new HashMap<>();

    static {
        registerProvider(DepthFirstProver.class);
        registerProvider(BreadthFirstProver.class);
        registerProvider(HeuristicSearch.class);
        registerProvider(TacticalHeuristicSearch.class);
    }

    private AutomaticProvers() {
    }

    /**
     * The main method for fetching an {@link AutomaticProver
     * automatic prover}.
     * <p>You can get the automatic provers by name.</p>
     * <p>This method throws an exception if the prover does not
     * exist.</p>
     * <p><span style="font-weight:bold">Note</span>: use {@link
     * AutomaticProvers#getProvider(java.lang.String)} to get more information
     * about the prover before fetching an actual one.</p>
     *
     * @param prover the name of the automatic prover to fetch.
     * @return an {@link AutomaticProver automatic prover} that operates on euler
     *         diagrams.
     */
    public static AutomaticProver getAutomaticProver(String prover) {
        if (prover == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "prover"));
        }
        AutomaticProverProvider provider = providers.get(prover);
        return provider.getAutomaticProver();
    }

    /**
     * Returns the {@link AutomaticProverProvider automatic prover provider} of the
     * given name.
     * <p>Returns {@code null} if no such provider exists.</p>
     * <p><span style="font-weight:bold">Note</span>: the returned provider
     * contains a plethora of information about the automatic prover (e.g.: what it does).</p>
     *
     * @param prover the name of the prover for which to fetch
     *                      the provider.
     * @return the provider for the desired prover.
     *         <p>Returns {@code null} if no such provider exists.</p>
     */
    public static AutomaticProverProvider getProvider(String prover) {
        return providers.get(prover);
    }

    /**
     * Returns a set of names of all currently supported automatic provers.
     * <p>To get information about a particular prover, use the
     * {@link AutomaticProvers#getProvider(java.lang.String)} method.</p>
     * <p>Note: This method never returns {@code null}.</p>
     *
     * @return a set of names of all currently supported provers.
     */
    public static Set<String> getKnownAutomaticProvers() {
        return Collections.unmodifiableSet(providers.keySet());
    }

    /**
     * Registers an instance of the given {@link AutomaticProverProvider} class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old automatic prover providers that happen to
     * have the same name as the newly registered one.</p>
     *
     * @param providerClass the automatic prover provider to register.
     */
    public static void registerProvider(Class<?> providerClass) {
        if (providerClass == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "providerClass"));
        }
        try {
            @SuppressWarnings("unchecked")
            AutomaticProverProvider theProvider = providerClass.asSubclass(AutomaticProverProvider.class).getConstructor().newInstance();
            synchronized (providers) {
                providers.put(theProvider.getAutomaticProverName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }
}
