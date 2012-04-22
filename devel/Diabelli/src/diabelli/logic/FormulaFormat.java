/*
 * File name: FormulaFormat.java
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
package diabelli.logic;

import org.netbeans.api.annotations.common.NonNull;

/**
 * Provides meta-information about the format in which {@link
 * FormulaRepresentation#getFormula() formulae} may be encoded.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface FormulaFormat {

    /**
     * Returns the name of the format. This name should be unique across all
     * Diabelli components. When reasoners register their formats in {@link
     * FormulaFormatManager the formula format manager} this name will be used
     * as the unique key that identifies the format. If another reasoner tries
     * to register a format with the same name, then an exception will be
     * raised.
     *
     * <p>Some examples: <ul> <li>Isabelle 2011-1 term tree:
     * Isabelle_term_tree,</li> <li>Isabelle 2011-1 pretty formula string:
     * Isabelle2011_1_pretty_string,</li> <li>Speedith's spider diagram objects:
     * Speedith_sd, and</li> <li>Speedith's spider diagram text format:
     * Speedith_sd_text.</li> </ul></p>
     * @return the name of the format.
     */
    @NonNull
    String getFormatName();

    /**
     * Returns a human-readable name of this formula format. This string will be
     * displayed to the user in the GUI.
     *
     * <p>Some examples: <ul> <li>Isabelle 2011-1 term tree:
     * <span
     * style="font-style:italic;">Isabelle</span>,</li> <li>Isabelle 2011-1 pretty formula string:
     * <span style="font-style:italic;">Isabelle (pretty
     * text)</span>,</li> <li>Speedith's spider diagram objects:
     * <span
     * style="font-style:italic;">Spider diagrams</span>, and</li> <li>Speedith's spider diagram text format:
     * <span
     * style="font-style:italic;">Spider diagrams (text)</span>,</li> </ul></p>
     * @return a human-readable name of this formula format.
     */
    @NonNull
    String getPrettyName();

    /**
     * Returns the type of {@link FormulaRepresentation#getFormula() the raw
     * formula} for this format.
     * @return the type of {@link FormulaRepresentation#getFormula() the raw
     * formula} for this format.
     */
    Class<?> getRawFormulaType();
    
}
