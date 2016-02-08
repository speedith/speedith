/*
 *   Project: Speedith.Core
 * 
 * File name: SDExporter.java
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

import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.CharsetEncoder;

import static speedith.core.i18n.Translations.i18n;

/**
 * The class defining the interface of all spider diagram text exporters.
 * <p>This class also provides some default behaviour for some of the methods.
 * Only one method (namely {@link SDExporter#exportTo(speedith.core.lang.SpiderDiagram, java.io.Writer)})
 * needs to be implemented in deriving classes.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SDExporter {

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and returns the latter as a Java string.
     * <p>The default implementation of this method simply calls
     * {@link SDExporter#exportTo(speedith.core.lang.SpiderDiagram, java.io.Writer) }
     * with a {@link StringWriter}.</p>
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @return the textual form of the given spider diagram.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     */
    public String export(SpiderDiagram spiderDiagram) throws ExportException {
        StringWriter sw = new StringWriter();
        try {
            exportTo(spiderDiagram, sw);
        } catch (IOException ex) {
            throw new RuntimeException(i18n("GERR_ILLEGAL_STATE"));
        }
        return sw.toString();
    }

    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and writes the latter to the given {@link OutputStream output}.
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @param output the object to which to write the textual form of the
     * spider diagram to.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     * @throws IOException this exception is thrown if an error occurred during
     * writing to the output.
     */
    public void exportTo(SpiderDiagram spiderDiagram, OutputStream output) throws IOException, ExportException {
        exportTo(spiderDiagram, new OutputStreamWriter(output));
    }

    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and writes the latter to the given {@link OutputStream output}.
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @param output the object to which to write the textual form of the
     * spider diagram to.
     * @param encoding the character encoding to use when outputting.
     * @throws UnsupportedEncodingException this exception is thrown if (yes,
     * you've guessed it) the encoding is not supported.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     * @throws IOException this exception is thrown if an error occurred during
     * writing to the output.
     */
    public void exportTo(SpiderDiagram spiderDiagram, OutputStream output, String encoding) throws UnsupportedEncodingException, IOException, ExportException {
        exportTo(spiderDiagram, new OutputStreamWriter(output, encoding));
    }

    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and writes the latter to the given {@link OutputStream output}.
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @param output the object to which to write the textual form of the
     * spider diagram to.
     * @param encoding the character encoding to use when outputting.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     * @throws IOException this exception is thrown if an error occurred during
     * writing to the output.
     */
    public void exportTo(SpiderDiagram spiderDiagram, OutputStream output, Charset encoding) throws IOException, ExportException {
        exportTo(spiderDiagram, new OutputStreamWriter(output, encoding));
    }

    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and writes the latter to the given {@link OutputStream output}.
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @param output the object to which to write the textual form of the
     * spider diagram to.
     * @param encoding the character encoder to use when outputting.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     * @throws IOException this exception is thrown if an error occurred during
     * writing to the output.
     */
    public void exportTo(SpiderDiagram spiderDiagram, OutputStream output, CharsetEncoder encoding) throws IOException, ExportException {
        exportTo(spiderDiagram, new OutputStreamWriter(output, encoding));
    }

    /**
     * Takes a {@link SpiderDiagram spider diagram}, converts it to a textual
     * form, and writes the latter to the given {@link Writer output}.
     * @param spiderDiagram the spider diagram to export to a textual form.
     * @param output the object to which to write the textual form of the
     * spider diagram to.
     * @throws ExportException thrown by the exporter if the exporting of the
     * spider diagram failed for some reason.
     * @throws IOException this exception is thrown if an error occurred during
     * writing to the output.
     */
    public abstract void exportTo(SpiderDiagram spiderDiagram, Writer output) throws ExportException, IOException;
    // </editor-fold>
}
