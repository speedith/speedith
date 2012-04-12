/*
 * File name: FormulaRepresentation.java
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
import org.openide.util.NbBundle;

/**
 * Contains {@link FormulaRepresentation#getFormula() a formula} and {@link 
 * FormulaRepresentation#getFormat() a descriptor} of the format in which the
 * formula is encoded.
 * @param <T> the type of the {@link FormulaRepresentation#getFormula() raw formula}.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class FormulaRepresentation<T> {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    private final T formula;
    private final FormulaFormatDescriptor format;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new representation description object for the given formula.
     * This class carries the formula itself together with some meta-information
     * about the format in which the formula is encoded. For example, the
     * formula could be a string in the syntax of a particular theorem prover,
     * also, it could be an abstract syntax tree etc.
     *
     * @param formula the raw formula.
     * @param format the description of the format in which the raw formula is
     * encoded.
     */
    @NbBundle.Messages({
        "FP_formula_null=A valid, non-null formula object must be provided.",
        "FP_format_null=A valid, non-null format description of the formula must be provided."
    })
    public FormulaRepresentation(@NonNull T formula, @NonNull FormulaFormatDescriptor format) {
        if (formula == null) {
            throw new IllegalArgumentException(Bundle.FP_formula_null());
        }
        if (format == null) {
            throw new IllegalArgumentException(Bundle.FP_format_null());
        }
        this.formula = formula;
        this.format = format;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the actual raw formula, which is encoded in the {@link FormulaFormatDescriptor
     * described format}.
     *
     * @return the actual raw formula.
     */
    @NonNull
    public T getFormula() {
        return formula;
    }

    /**
     * Returns an object that describes the format in which the {@link FormulaRepresentation#getFormula()
     * formula} is encoded.
     *
     * @return an object that describes the format in which the {@link FormulaRepresentation#getFormula()
     * formula} is encoded.
     */
    @NonNull
    public FormulaFormatDescriptor getFormat() {
        return format;
    }
    //</editor-fold>
}
