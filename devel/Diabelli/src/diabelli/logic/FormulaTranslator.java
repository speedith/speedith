/*
 * File name: FormulaTranslator.java
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

import diabelli.Diabelli;
import diabelli.components.DiabelliComponent;
import java.util.ArrayList;
import java.util.List;
import org.netbeans.api.annotations.common.NonNull;
import org.openide.util.NbBundle;

/**
 * Formula translators provide translation capabilities to Diabelli. Available
 * translators may be registered by {@link DiabelliComponent Diabelli components}
 * that implement the {@link diabelli.components.FormulaTranslationsProvider formula
 * translations provider interface}. {@link Diabelli#getFormulaFormatManager() The
 * formula format manager} will pick all these components up, fetch their
 * translators, and register them for later automatic use in Diabelli.
 *
 * <p>Diabelli will try to automatically translate all goals, premises, and
 * conclusions, that the user deliberately inspects.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class FormulaTranslator {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    private final FormulaFormatDescriptor fromFormat;
    private final FormulaFormatDescriptor toFormat;
    private final TranslationType type;
    private final String name;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises this formula format translator with the meta-information
     * about what it does.
     *
     * @param fromFormat the format from which this translator is able to
     * translate formulae.
     * @param toFormat the format into which this translator is able to
     * translate formulae.
     * @param type the type of this translation. A translation may be {@link
     * TranslationType#ToEquivalent equivalent}, {@link
     * TranslationType#ToEntailing entailing}, or {@link
     * TranslationType#ToEntailed entailed}. Which translation may be used when
     * depends on whether the original formula is a premise, a conclusion, or
     * the whole formula.
     * @param name an internal and unique name for this translator.
     */
    @NbBundle.Messages({
        "FT_fromFormat_null=The source format of the translation is not specified.",
        "FT_toFormat_null=The destination format of the translation is not specified.",
        "FT_type_null=The type of the translation is not specified.",
        "FT_name_null=The name of this translator is not specified."
    })
    protected FormulaTranslator(@NonNull FormulaFormatDescriptor fromFormat, @NonNull FormulaFormatDescriptor toFormat, @NonNull TranslationType type, @NonNull String name) {
        if (fromFormat == null) {
            throw new IllegalArgumentException(Bundle.FT_fromFormat_null());
        }
        if (toFormat == null) {
            throw new IllegalArgumentException(Bundle.FT_toFormat_null());
        }
        if (type == null) {
            throw new IllegalArgumentException(Bundle.FT_type_null());
        }
        if (name == null || name.isEmpty()) {
            throw new IllegalArgumentException(Bundle.FT_name_null());
        }
        this.fromFormat = fromFormat;
        this.toFormat = toFormat;
        this.type = type;
        this.name = name;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns the format from which this translator is able to translate
     * formulae.
     *
     * @return the format from which this translator is able to translate
     * formulae.
     */
    @NonNull
    public FormulaFormatDescriptor getFromFormat() {
        return fromFormat;
    }

    /**
     * Returns the format into which this translator is able to translate
     * formulae.
     *
     * @return the format into which this translator is able to translate
     * formulae.
     */
    @NonNull
    public FormulaFormatDescriptor getToFormat() {
        return toFormat;
    }

    /**
     * Returns the type of this translation. A translation may be {@link
     * TranslationType#ToEquivalent equivalent}, {@link
     * TranslationType#ToEntailing entailing}, or {@link
     * TranslationType#ToEntailed entailed}. Which translation may be used when
     * depends on whether the original formula is a premise, a conclusion, or
     * the whole formula.
     *
     * @return the type of this translation.
     */
    @NonNull
    public TranslationType getTranslationType() {
        return type;
    }

    /**
     * Returns the internal and unique name for this translator.
     *
     * @return the internal and unique name for this translator.
     */
    @NonNull
    public String getName() {
        return name;
    }

    /**
     * Returns a human-readable description that may be displayed in the GUI
     * through tool-tips.
     *
     * @return a human-readable description that may be displayed in the GUI
     * through tool-tips.
     */
    @NonNull
    public abstract String getDescription();

    /**
     * Returns a human-readable name that may be displayed in the GUI. Possibly
     * in lists of available translations. This string should be as short as
     * possible.
     *
     * @return a human-readable name that may be displayed in the GUI.
     */
    @NonNull
    public abstract String getPrettyName();

    /**
     * Translates the given formula (in the {@link
     * FormulaTranslator#getFromFormat() source format}) into a formula in the
     * {@link FormulaTranslator#getToFormat() target format}.
     *
     * @param formula the formula to translate.
     * @return the translated formulae.
     * @throws diabelli.logic.FormulaTranslator.TranslationException This
     * exception is thrown whenever the translation didn't succeed for any
     * reason. A detailed explanation might be given for the user.
     */
    public abstract Formula translate(Formula formula) throws TranslationException;

    /**
     * Translates the given formulae (in the {@link
     * FormulaTranslator#getFromFormat() source format}) into formulae in the {@link FormulaTranslator#getToFormat() target format}.
     * <p>If more than one formula is returned, it is assumed that the formulae
     * are conjunctively composed. This is used only for premises and the
     * {@link TranslationType#ToEquivalent} and {@link TranslationType#ToEntailed}
     * translation types.</p>
     *
     * @param formulae the formulae to translate.
     * @return the translated formulae.
     * @throws diabelli.logic.FormulaTranslator.TranslationException This
     * exception is thrown whenever the translation didn't succeed for any
     * reason. A detailed explanation might be given for the user.
     */
    public abstract ArrayList<Formula> translate(List<Formula> formulae) throws TranslationException;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    /**
     * The translation type of particular {@link FormulaTranslator formula
     * translators}.
     */
    public static enum TranslationType {

        /**
         * Indicates that the translated formula is semantically equivalent to
         * the original one.
         */
        ToEquivalent,
        /**
         * Indicates that the translated formula is semantically entailed
         * (implied) by the original one.
         */
        ToEntailed,
        /**
         * Indicates that the translated formula is semantically entailing
         * (implies) the original one.
         */
        ToEntailing;
    }

    /**
     * This exception gives a detailed explanation as to why a translation did
     * not succeed. The message may be displayed to the user in the GUI.
     */
    public static class TranslationException extends Exception {

        public TranslationException() {
        }

        public TranslationException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
            super(message, cause, enableSuppression, writableStackTrace);
        }

        public TranslationException(Throwable cause) {
            super(cause);
        }

        public TranslationException(String message, Throwable cause) {
            super(message, cause);
        }

        public TranslationException(String message) {
            super(message);
        }
    }
    //</editor-fold>
}
