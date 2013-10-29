/*
 *   Project: Speedith
 * 
 * File name: DiagramSelector.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
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
package speedith.ui.selection.helpers;

import java.awt.Frame;
import java.util.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.core.reasoning.args.selection.SelectionSequence;
import static speedith.i18n.Translations.i18n;

/**
 * A class full of convenience methods for obtaining fully specified selection
 * steps and procedures that translate the resulting selection into rule
 * arguments.
 *
 * <p>Implementations of this class must provide at least the default
 * constructor.</p>
 *
 * @param <T> the type of rule this object produces given a selection sequence
 * of diagrammatic elements.
 * @author Matej Urbas [matej.urbas@gmail.com]
 * @deprecated Should use the mechanism that comes with {@link speedith.core.reasoning.InferenceRuleProvider
 * inference rule providers}. See {@link speedith.core.reasoning.InferenceRuleProvider#getInstructions() }.
 */
@Deprecated
public abstract class DiagramSelector<T extends RuleArg> {

    // <editor-fold defaultstate="collapsed" desc="The Selection Conversion Interface">
    /**
     * Converts the given selection sequence to a rule argument.
     *
     * @param selection a collection of selected diagram elements.
     * @return the resulting rule argument.
     * @throws IllegalArgumentException thrown if the selection sequence cannot
     * be converted to a rule argument because it's either {@code null}, faulty,
     * or incomplete in any sense.
     */
    public abstract T convertToRuleArg(SelectionSequence selection);

    /**
     * Shows the selection dialog for the given diagram and returns the specific
     * rule arguments.
     *
     * @param parent the frame that should "host" the dialog.
     * @param diagram the diagram from which the user should select the spiders.
     * @return the rule arguments as selected by the user. If the user cancelled
     * the selection {@code null} will be returned.
     */
    public abstract T showSelectionDialog(Frame parent, SpiderDiagram diagram);
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Factory Methods">
    // <editor-fold defaultstate="collapsed" desc="Factory-Related Fields">
    /**
     * The map containing all currently registered GUI selection providers.
     */
    private static final HashMap<Class<? extends RuleArg>, TreeMap<String, Class<? extends DiagramSelector>>> providersByRuleArg = new HashMap<Class<? extends RuleArg>, TreeMap<String, Class<? extends DiagramSelector>>>();
    private static final HashMap<String, Class<? extends DiagramSelector>> providersByName = new HashMap<String, Class<? extends DiagramSelector>>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Static Constructor">
    static {
        registerProvider(SpiderRegionSelector.class);
    }
    // </editor-fold>

    /**
     * The main method for fetching {@link DiagramSelector diagram GUI selectors}.
     * <p>You can get the selectors by the type of the argument they
     * produce.</p> <p>This method throws an exception if the selector does not
     * exist for the given type.</p>
     *
     * @param <TArg> The type of {@link RuleArg rule argument} we want the user
     * to select from a GUI.
     * @param ruleArgs rule arguments for which to get the selector.
     * @param selectorArgs the arguments that will be passed to the selector's
     * constructor upon creation.
     * @return a {@link DiagramSelector GUI diagram element selector} provides a
     * GUI for selecting diagrammatic elements and returns the rule arguments of
     * the desired type.
     */
    @SuppressWarnings("unchecked")
    public static <TArg extends RuleArg> DiagramSelector<TArg> getSelector(Class<TArg> ruleArgs, Object... selectorArgs) {
        if (ruleArgs == null) {
            throw new IllegalArgumentException(speedith.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "ruleArgs"));
        }

        // Check that there is exactly one selector.
        TreeMap<String, Class<? extends DiagramSelector>> providers = providersByRuleArg.get(ruleArgs);
        if (providers == null || providers.isEmpty()) {
            throw new IllegalArgumentException(i18n("SELECTOR_NO_PROVIDERS_FOR_THIS_TYPE"));
        } else if (providers.size() > 1) {
            throw new IllegalArgumentException(i18n("SELECTOR_AMBIGUOUS"));
        }
        // Now instantiate the selector.
        return instantiateSelector(selectorArgs, (Class<? extends DiagramSelector<TArg>>) providers.firstEntry().getValue());
    }

    /**
     * The main method for fetching {@link DiagramSelector diagram GUI selectors}.
     * <p>You can get the selectors by the type of the argument they
     * produce.</p> <p>This method throws an exception if the selector does not
     * exist for the given type.</p>
     *
     * @param <TArg> The type of {@link RuleArg rule argument} we want the user
     * to select from a GUI.
     * @param name the name of the GUI diagram selector provider to create.
     * @param selectorArgs the arguments that will be passed to the selector's
     * constructor upon creation.
     * @return a {@link DiagramSelector GUI diagram element selector} provides a
     * GUI for selecting diagrammatic elements and returns the rule arguments of
     * the desired type.
     */
    @SuppressWarnings("unchecked")
    public static <TArg extends RuleArg> DiagramSelector<TArg> getSelector(String name, Object... selectorArgs) {
        if (name == null) {
            throw new IllegalArgumentException(speedith.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "name"));
        }

        // Now instantiate the selector.
        return instantiateSelector(selectorArgs, (Class<? extends DiagramSelector<TArg>>) providersByName.get(name));
    }

    /**
     * Returns a set of {@link RuleArg} types for which built-in selectors
     * exist.
     *
     * @return
     */
    public static Set<Class<? extends RuleArg>> getSupportedRuleArgs() {
        return Collections.unmodifiableSet(providersByRuleArg.keySet());
    }

    public static Collection<Class<? extends DiagramSelector>> getSelectors(Class<? extends RuleArg> aClass) {
        TreeMap<String, Class<? extends DiagramSelector>> selectors = providersByRuleArg.get(aClass);
        if (selectors == null) {
            return null;
        } else {
            return Collections.unmodifiableCollection(selectors.values());
        }
    }

    static Collection<Class<? extends DiagramSelector>> getRegisteredSelectors() {
        return Collections.unmodifiableCollection(providersByName.values());
    }

    public static String getSelectorName(Class<? extends DiagramSelector> selector) {
        SelectorDetails desc = selector.getAnnotation(SelectorDetails.class);
        return desc.name();
    }

    /**
     * Registers a {@link DiagramSelector GUI selector provider} class. <p>This
     * method throws an exception if the method failed for any reason.</p>
     *
     * @param providerClass the GUI diagram selector provider to register.
     */
    public static void registerProvider(Class<? extends DiagramSelector> providerClass) {
        if (providerClass == null) {
            throw new IllegalArgumentException(speedith.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "providerClass"));
        }
        // Get the 'SelectorDetails' annotation from the class:
        SelectorDetails desc = providerClass.getAnnotation(SelectorDetails.class);
        if (desc == null) {
            throw new IllegalArgumentException(i18n("SELECTOR_NEEDS_ANNOTATION"));
        }
        if (desc.targetRuleArg() == null || !RuleArg.class.isAssignableFrom(desc.targetRuleArg())) {
            throw new IllegalArgumentException(i18n("SELECTOR_TARGET_RULE_ARG_WRONG"));
        }
        if (desc.name() == null || desc.name().isEmpty()) {
            throw new IllegalArgumentException(i18n("SELECTOR_NAME_EMPTY"));
        }
        synchronized (providersByRuleArg) {
            if (providersByName.containsKey(desc.name())) {
                throw new IllegalArgumentException(i18n("SELECTOR_ALREADY_REGISTERED", desc.name()));
            }
            providersByName.put(desc.name(), providerClass);
            TreeMap<String, Class<? extends DiagramSelector>> ruleArgs = providersByRuleArg.get(desc.targetRuleArg());
            if (ruleArgs == null) {
                providersByRuleArg.put(desc.targetRuleArg(), ruleArgs = new TreeMap<String, Class<? extends DiagramSelector>>());
            }
            ruleArgs.put(desc.name(), providerClass);
        }
    }

    //<editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    private static <TArg extends RuleArg> DiagramSelector<TArg> instantiateSelector(Object[] selectorArgs, Class<? extends DiagramSelector<TArg>> selector) throws IllegalArgumentException {
        if (selector == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "selector"));
        }
        if (selectorArgs == null || selectorArgs.length == 0) {
            try {
                return selector.getConstructor().newInstance();
            } catch (Exception ex) {
                throw new IllegalArgumentException(i18n("SELECTOR_COULD_NOT_INSTANTIATE"), ex);
            }
        } else {
            Class[] classes = new Class[selectorArgs.length];
            for (int i = 0; i < selectorArgs.length; i++) {
                Object argI = selectorArgs[i];
                classes[i] = argI == null ? Object.class : argI.getClass();
            }
            try {
                return (DiagramSelector<TArg>) selector.getConstructor(classes).newInstance(selectorArgs);
            } catch (Exception ex) {
                throw new IllegalArgumentException(i18n("SELECTOR_COULD_NOT_INSTANTIATE"), ex);
            }
        }
    }
    //</editor-fold>
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Static Methods for getting built-in selectors">
    /**
     * Returns a selection provider for selecting feet of a spider in a diagram.
     * This can be used for example in the {@link SplitSpiders} rule.
     *
     * @return
     */
    public static DiagramSelector<SpiderRegionArg> getSpiderRegionSelector() {
        return SpiderRegionSelector.Instance;
    }
    // </editor-fold>
}
