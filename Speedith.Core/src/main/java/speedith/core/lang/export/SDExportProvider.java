/*
 *   Project: Speedith.Core
 * 
 * File name: SDExportProvider.java
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

import java.util.Locale;
import java.util.Map;
import java.util.SortedSet;

/**
 * This is the base of the classes that provide actual exporters for the
 * mechanism for exporting {@link SpiderDiagram spider diagrams}. <p>See {@link SDExporting}
 * for detailed description on how to register new export providers.</p>
 * <p><span style="font-weight:bold">Important</span>: implementations of this
 * class should have a <span style="font-style:italic;">public default
 * constructor</span>.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SDExportProvider {

    /**
     * Returns the name of the format to which {@link SDExporter exporters} from
     * this provider export spider diagrams to.
     *
     * @return the name of the format to which {@link SDExporter exporters} from
     * this provider export spider diagrams to.
     */
    public abstract String getFormatName();

    /**
     * Creates an exporter of spider diagrams. This exporter will export spider
     * diagrams to the format as indicated by
     * {@link SDExportProvider#getFormatName()}.
     *
     * @param parameters optional parameters, which can be considered by the
     * export provider when constructing the exporter. <p>A list of valid
     * parameters can be inspected via {@link
     * SDExportProvider#getParameters()}. Description of every parameter can be
     * obtained via {@link SDExportProvider#getParameterDescription(java.lang.String, java.util.Locale)}.</p>
     * <p><span style="font-weight:bold">Note</span>: this parameter may be
     * {@code null}, which indicates that an exporter with no parameters should
     * be returned.</p>
     * @return an exporter of spider diagrams. This exporter will export spider
     * diagrams to the format as indicated by
     * {@link SDExportProvider#getFormatName()}.
     */
    public abstract SDExporter getExporter(Map<String, String> parameters);

    /**
     * Returns a set of parameter names that are meaningful to {@link SDExportProvider#getExporter(java.util.Map)}.
     * <p>This method may return {@code null}, which indicates that no
     * parameters are taken by {@link SDExportProvider#getExporter(java.util.Map)}.</p>
     * <p>Note: the default implementation returns {@code null}.</p>
     *
     * @return a set of parameter names that are meaningful to {@link SDExportProvider#getExporter(java.util.Map)}.
     */
    public SortedSet<String> getParameters() {
        return null;
    }

    /**
     * Gets the description for the given parameter (which is in the
     * {@link SDExportProvider#getParameters()} set). <p>The default
     * implementation returns {@code null}</p>
     *
     * @param parameter the parameter for which we want a description.
     * @param locale the locale in which the description should be given.
     * @return the description of the parameter with the given name in the given
     * locale.
     */
    public String getParameterDescription(String parameter, Locale locale) {
        return null;
    }

    /**
     * Gets the description for the given parameter (which is in the
     * {@link SDExportProvider#getParameters()} set). <p>The default
     * implementation calls {@link SDExportProvider#getParameterDescription(java.lang.String, java.util.Locale)}
     * with the {@link Locale#getDefault() default locale}.</p>
     *
     * @param parameter the parameter for which we want a description.
     * @return the description of the parameter with the given name in the
     * default locale.
     */
    public String getParameterDescription(String parameter) {
        return getParameterDescription(parameter, Locale.getDefault());
    }

    /**
     * Returns the description of this export format. <p>This method calls {@link SDExportProvider#getDescription(java.util.Locale)}
     * with the {@link Locale#getDefault() default locale}.</p>
     *
     * @return the description of this export format.
     */
    public String getDescription() {
        return getDescription(Locale.getDefault());
    }

    /**
     * Returns the description of this export format in the given {@link Locale
     * locale}.
     *
     * @param locale the locale in which to give the description of this export
     * format.
     * @return the description of this export format in the given {@link Locale
     * locale}.
     */
    public abstract String getDescription(Locale locale);
}
