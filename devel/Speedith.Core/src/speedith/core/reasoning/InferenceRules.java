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

import speedith.core.lang.export.SDExporting;
import speedith.core.reasoning.rules.SplitSpiders;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.InputStream;
import java.util.Collections;
import java.util.Set;
import java.util.HashMap;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.rules.AddFeet;
import speedith.core.reasoning.rules.Idempotency;
import static speedith.core.i18n.Translations.*;

/**
 * Contains a list of available {@link InferenceRule inference rules}, provides
 * detailed information about them (through their respective {@link
 * InferenceRuleProvider inference rule provider}) and acts as a means to
 * construct/fetch/instantiate inference rules for actual use in proofs.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class InferenceRules {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The map containing all currently registered inference rule providers.
     */
    private static final HashMap<String, InferenceRuleProvider<? extends RuleArg>> providers = new HashMap<String, InferenceRuleProvider<? extends RuleArg>>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    static {
        // Register built-in inference rules.
        registerProvider(SplitSpiders.class);
        registerProvider(AddFeet.class);
        registerProvider(Idempotency.class);
    }

    /**
     * This is a 'static' class. No instantiation needed.
     */
    private InferenceRules() {
    }
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * The path to the file in the META-INF folder (within the JAR file) listing
     * the class names of the {@link InferenceRuleProvider inference rule
     * providers} that should be registered.
     * <p>Each line should be a fully qualified name of the {@link InferenceRuleProvider}'s
     * class that should be registered within Speedith's reasoning kernel.</p>
     */
    public static final String InferenceRuleProvidersRegistry = "META-INF/speedith/InferenceRuleProviders";

    /**
     * The main method for fetching a Spider-diagrammatic {@link InferenceRule
     * inference rule}.
     * <p>You can get the inference rules by name.</p>
     * <p>This method throws an exception if the inference rule does not
     * exist.</p>
     * <p><span style="font-weight:bold">Note</span>: use {@link
     * InferenceRules#getProvider(java.lang.String)} to get more information
     * about the inference rule before fetching an actual one.</p>
     * @param inferenceRule the name of the inference rule to fetch.
     * @return an {@link InferenceRule inference rule} that operates on spider
     * diagrams.
     */
    public static InferenceRule<? extends RuleArg> getInferenceRule(String inferenceRule) {
        InferenceRuleProvider<? extends RuleArg> provider = providers.get(inferenceRule);
        if (inferenceRule == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "inferenceRule"));
        }
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
     * @param inferenceRule the name of the inference rule for which to fetch
     * the provider.
     * @return the provider for the desired inference rule.
     * <p>Returns {@code null} if no such provider exists.</p>
     */
    public static InferenceRuleProvider<? extends RuleArg> getProvider(String inferenceRule) {
        return providers.get(inferenceRule);
    }

    /**
     * Returns a set of names of all currently supported inference rules.
     * <p>To get information about a particular inference rule, use the
     * {@link InferenceRules#getProvider(java.lang.String)} method.</p>
     * @return a set of names of all currently supported inference rules.
     */
    public static Set<String> getKnownInferenceRules() {
        return Collections.unmodifiableSet(providers.keySet());
    }

    /**
     * Scans for class names in the manifest resource file at the path given by
     * {@link SDExporting#InferenceRuleProvidersRegistry}. Found class names are
     * looked up, loaded, and registered as inference rule providers.
     * <p>This method throws an exception if the scan failed for some
     * reason.</p>
     */
    public static void scanForInferenceRules() {
        InputStream registryStream = Thread.currentThread().getContextClassLoader().getResourceAsStream(InferenceRuleProvidersRegistry);
        if (registryStream != null) {
            BufferedReader registryReader = new BufferedReader(new InputStreamReader(registryStream));
            scanForInferenceRules(registryReader);
        }
    }

    /**
     * Scans for class names in the given file.
     * <p>Each line must be a fully qualified name of a class that implements
     * the {@link InferenceRuleProvider} interface.</p>
     * Found classes are loaded and registered as inference rule providers.
     * <p>This method throws an exception if the scan failed for some
     * reason.</p>
     * @param classNames a reader of class names (each line must be a fully
     * qualified name of a class that implements the {@link
     * InferenceRuleProvider} interface.).
     * @throws RuntimeException thrown if the classes read from the given reader
     * could not have been loaded for some reason.
     */
    public static void scanForInferenceRules(BufferedReader classNames) throws RuntimeException {
        try {
            String line = classNames.readLine();
            while (line != null) {
                registerProvider(line);
                line = classNames.readLine();
            }
        } catch (Exception ex) {
            throw new RuntimeException(i18n("ERR_PROVIDER_SCAN_FAILED"), ex);
        } finally {
            try {
                classNames.close();
            } catch (IOException ex) {
                throw new RuntimeException(i18n("GERR_ILLEGAL_STATE"), ex);
            }
        }
    }

    /**
     * Registers an instance of the given {@link InferenceRuleProvider} class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old inference rule providers that happen to
     * have the same name as the newly registered one.</p>
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
                providers.put(theProvider.getInferenceRuleName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }

    /**
     * Registers an instance of the given {@link InferenceRuleProvider} class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old inference rule providers that happen to
     * have the same name as the newly registered one.</p>
     * @param className the name of the provider's class to register.
     * @throws ClassNotFoundException thrown if the class with the given name
     * could not have been found.
     */
    public static void registerProvider(String className) throws ClassNotFoundException {
        registerProvider(Class.forName(className));
    }
    // </editor-fold>
}
