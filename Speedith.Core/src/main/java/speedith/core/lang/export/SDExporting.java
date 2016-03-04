/*
 *   Project: Speedith.Core
 * 
 * File name: SDExporting.java
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
package speedith.core.lang.export;

import speedith.core.lang.SpiderDiagram;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * The factory class providing an entry point to obtaining {@link SDExporter
 * text exporters} for {@link SpiderDiagram spider diagrams}.
 * <p>This factory looks up a specific resource file in the JAR (see
 * {@link SDExporting#ExportProvidersRegistry}) where the class names
 * of {@link SDExportProvider}s are listed. These providers are then
 * instantiated and registered with this factory.</p>
 * <p>The {@link SDExporter exporter}s can then be used with via the method
 * {@link SDExporting#getExporter(java.lang.String)}, for example.</p>
 * <p>New
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class SDExporting {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The map containing all currently registered export providers.
     */
    private static final HashMap<String, SDExportProvider> providers = new HashMap<>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    static {
        // Register built-in exporters.
        registerProvider(Isabelle2011ExportProvider.class);
        registerProvider(OpenproofExportProvider.class);
    }

    /**
     * This is a 'static' class. No instantiation needed.
     */
    private SDExporting() {
    }
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * The path to the file in the META-INF folder (within the JAR file) listing
     * the class names of the {@link SDExportProvider text exporting
     * providers} that should be registered.
     * <p>Each line should be a fully qualified name of the {@link SDExportProvider}'s
     * class that should be registered for Speedith exporting.</p>
     */
    public static final String ExportProvidersRegistry = "META-INF/speedith/ExportProviders";

    /**
     * The main method to get a {@link SDExporter text exporter} of spider
     * diagrams.
     * <p>You can select the format to which to export.</p>
     * <p>This method throws an exception if the format does not exist.</p>
     * @param format the name of the format to which to export spider diagrams.
     * @return a {@link SDExporter text exporter} of spider
     * diagrams for the specified text format.
     */
    public static SDExporter getExporter(String format) {
        SDExportProvider provider = providers.get(format);
        if (format == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "format"));
        }
        return provider.getExporter(null);
    }

    /**
     * The main method to get a {@link SDExporter text exporter} of spider
     * diagrams.
     * <p>You can select the format to which to export.</p>
     * <p>This method throws an exception if the format does not exist.</p>
     * @param format the name of the format to which to export spider diagrams.
     * @param parameters the parameters to the exporter (given to {@link SDExportProvider#getExporter(java.util.Map)}).
     * <p>You may want to inspect the descriptions of parameters (see {@link SDExportProvider#getParameterDescription(java.lang.String, java.util.Locale)})
     * of the provider for this format. The latter can be fetched through the {@link SDExporting#getProvider(String)} method.</p>
     * @return a {@link SDExporter text exporter} of spider
     * diagrams for the specified text format.
     */
    public static SDExporter getExporter(String format, Map<String, String> parameters) {
        SDExportProvider provider = providers.get(format);
        if (format == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "format"));
        }
        return provider.getExporter(parameters);
    }

    /**
     * Returns the {@link SDExportProvider provider} for the given format.
     * <p>Returns {@code null} if no such provider exists.</p>
     * <p>The provider also provides more information about the format.</p>
     * @param format the format for which to fetch the export provider.
     * @return the provider for the given format.
     */
    public static SDExportProvider getProvider(String format) {
        return providers.get(format);
    }

    /**
     * Returns a set of all currently supported export formats.
     * <p>To get information about a particular format, use the
     * {@link SDExporting#getProvider(java.lang.String)} method with the format
     * name from the set which this method returns.</p>
     * @return a set of all currently supported export formats.
     */
    public static Set<String> getSupportedFormats() {
        return Collections.unmodifiableSet(providers.keySet());
    }

    /**
     * Scans for class names in the manifest resource file at the path given by
     * {@link SDExporting#ExportProvidersRegistry}. Found class names are looked
     * up, loaded, and registered.
     * <p>This method throws an exception if the scan failed for some
     * reason.</p>
     */
    public static void scanForExporters() {
        InputStream registryStream = Thread.currentThread().getContextClassLoader().getResourceAsStream(ExportProvidersRegistry);
        if (registryStream != null) {
            BufferedReader registryReader = new BufferedReader(new InputStreamReader(registryStream));
            try {
                String line = registryReader.readLine();
                while (line != null) {
                    registerProvider(line);
                    line = registryReader.readLine();
                }
            } catch (Exception ex) {
                throw new RuntimeException(i18n("ERR_PROVIDER_SCAN_FAILED"), ex);
            } finally {
                try {
                    registryReader.close();
                } catch (IOException ex) {
                }
            }
        }
    }

    /**
     * Registers the {@link SDExportProvider} represented by the given class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old export providers that happen to have
     * the same format name as the newly registered one.</p>
     * @param providerClass the export provider class to register.
     */
    public static void registerProvider(Class<?> providerClass) {
        if (providerClass == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "providerClass"));
        }
        try {
            SDExportProvider theProvider = providerClass.asSubclass(SDExportProvider.class).getConstructor().newInstance();
            synchronized (providers) {
                providers.put(theProvider.getFormatName(), theProvider);
            }
        } catch (Exception ex) {
            throw new IllegalArgumentException(i18n("ERR_EXPORT_PROVIDER_CLASS"), ex);
        }
    }

    /**
     * Registers the {@link SDExportProvider} represented by the given class.
     * <p>This method throws an exception if the method failed for any
     * reason.</p>
     * <p>This method replaces any old export providers that happen to have
     * the same format name as the newly registered one.</p>
     * @param className the name of the provider's class to register.
     * @throws ClassNotFoundException thrown if the class with the given name
     * could not have been found.
     */
    public static void registerProvider(String className) throws ClassNotFoundException {
        registerProvider(Class.forName(className));
    }
    // </editor-fold>
}
