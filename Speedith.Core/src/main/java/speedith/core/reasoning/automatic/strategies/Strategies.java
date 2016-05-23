package speedith.core.reasoning.automatic.strategies;

import java.util.Collections;
import java.util.HashMap;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class Strategies {
    public static final String strategy_preference = "strategy";

    private static final HashMap<String, StrategyProvider> providers = new HashMap<>();

    static {
        registerProvider(NoStrategy.class);
        registerProvider(BasicHeuristicStrategy.class);
        registerProvider(LowClutterStrategy.class);
        registerProvider(LengthStrategy.class);
    }

    private Strategies() {
    }

    /**
     * The main method for fetching a {@link Strategy
     * strategy for picking the next rule}.
     * <p>You can get the strategies by name.</p>
     * <p>This method throws an exception if the strategydoes not
     * exist.</p>
     * <p><span style="font-weight:bold">Note</span>: use {@link
     * Strategies#getProvider(java.lang.String)} to get more information
     * about the strategybefore fetching an actual one.</p>
     *
     * @param strategy the name of the strategy to fetch.
     * @return an {@link Strategy strategy} that operates on euler
     *         diagram inference rules.
     */
    public static Strategy getStrategy(String strategy) {
        if (strategy == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "strategy"));
        }
        StrategyProvider provider = providers.get(strategy);
        return provider.getStrategy();
    }

    /**
     * Returns the {@link StrategyProvider strategy provider} of the
     * given name.
     * <p>Returns {@code null} if no such provider exists.</p>
     * <p><span style="font-weight:bold">Note</span>: the returned provider
     * contains a plethora of information about the strategy (e.g.: what it does).</p>
     *
     * @param strategy the name of the strategy for which to fetch
     *                      the provider.
     * @return the provider for the desired strategy.
     *         <p>Returns {@code null} if no such provider exists.</p>
     */
    public static StrategyProvider getProvider(String strategy) {
        return providers.get(strategy);
    }

    /**
     * Returns a set of names of all currently supported strategies.
     * <p>To get information about a particular strategy, use the
     * {@link Strategies#getProvider(java.lang.String)} method.</p>
     * <p>Note: This method never returns {@code null}.</p>
     *
     * @return a set of names of all currently supported strategies.
     */
    public static Set<String> getKnownStrategies() {
        return Collections.unmodifiableSet(providers.keySet());
    }

    /**
     * Registers an instance of the given {@link StrategyProvider} class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old strategy providers that happen to
     * have the same name as the newly registered one.</p>
     *
     * @param providerClass the strategy provider to register.
     */
    public static void registerProvider(Class<?> providerClass) {
        if (providerClass == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "providerClass"));
        }
        try {
            @SuppressWarnings("unchecked")
            StrategyProvider theProvider = providerClass.asSubclass(StrategyProvider.class).getConstructor().newInstance();
            synchronized (providers) {
                providers.put(theProvider.getStrategyName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }
}
