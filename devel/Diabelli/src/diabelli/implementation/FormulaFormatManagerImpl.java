/*
 * File name: Class.java
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
package diabelli.implementation;

import diabelli.Diabelli;
import diabelli.FormulaFormatManager;
import diabelli.components.DiabelliComponent;
import diabelli.components.FormulaFormatsProvider;
import diabelli.components.FormulaTranslationsProvider;
import diabelli.components.GoalProvidingReasoner;
import diabelli.logic.FormulaFormatDescriptor;
import diabelli.logic.FormulaTranslator;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import org.openide.util.NbBundle;

/**
 * Diabelli's main implementation of the {@link FormulaFormatManager}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
class FormulaFormatManagerImpl implements FormulaFormatManager, ManagerInternals {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    private final HashMap<String, FormulaFormatDescriptor> formulaFormats;
    private final HashMap<String, FormulaTranslator> formulaTranslators;
    private final Diabelli diabelli;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    FormulaFormatManagerImpl(Diabelli diabelli) {
        if (diabelli == null) {
            throw new IllegalArgumentException(Bundle.Manager_diabelli_null());
        }
        this.diabelli = diabelli;
        this.formulaFormats = new HashMap<String, FormulaFormatDescriptor>();
        this.formulaTranslators = new HashMap<String, FormulaTranslator>();
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Formula Formats">
    @Override
    public Collection<FormulaFormatDescriptor> getFormulaFormats() {
        return Collections.unmodifiableCollection(formulaFormats.values());
    }

    /**
     * Registers the given formats with this manager. This method throws an
     * exception if any of the formats is already present.
     */
    @NbBundle.Messages({
        "FFM_format_already_exists=The Diabelli component '{0}' tried to register the formula format '{1}', which is already registered.",
        "FFM_formats_empty=The Diabelli component '{0}' advertises itself as a formula format provider, however, it provides no formats.",
        "FFM_format_null=The Diabelli component '{0}' tried to register a 'null' format."
    })
    void registerFormulaFormats(Collection<FormulaFormatDescriptor> formats, FormulaFormatsProvider providingComponent) {
        if (formats == null || formats.isEmpty()) {
            throw new IllegalArgumentException(Bundle.FFM_formats_empty(providingComponent.getName()));
        } else {
            for (FormulaFormatDescriptor format : formats) {
                if (format == null) {
                    throw new IllegalArgumentException(Bundle.FFM_format_null(providingComponent.getName()));
                }
                if (formulaFormats.containsKey(format.getFormatName())) {
                    throw new IllegalArgumentException(Bundle.FFM_format_already_exists(providingComponent.getName(), format.getFormatName()));
                }
                formulaFormats.put(format.getFormatName(), format);
            }
        }
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Formula Translators">
    @Override
    public Collection<FormulaTranslator> getFormulaTranslators() {
        return Collections.unmodifiableCollection(formulaTranslators.values());
    }

    /**
     * Registers the given formats with this manager. This method throws an
     * exception if any of the formats is already present.
     */
    @NbBundle.Messages({
        "FFM_translator_already_exists=The Diabelli component '{0}' tried to register the formula translator '{1}', which is already registered.",
        "FFM_translators_empty=The Diabelli component '{0}' advertises itself as a formula translator provider, however, it provides no formula translators.",
        "FFM_translator_null=The Diabelli component '{0}' tried to register a 'null' formula translator."
    })
    void registerFormulaTranslators(Collection<FormulaTranslator> translators, FormulaTranslationsProvider providingComponent) {
        if (translators == null || translators.isEmpty()) {
            throw new IllegalArgumentException(Bundle.FFM_translators_empty(providingComponent.getName()));
        } else {
            for (FormulaTranslator translator : translators) {
                if (translator == null) {
                    throw new IllegalArgumentException(Bundle.FFM_translator_null(providingComponent.getName()));
                }
                if (formulaTranslators.containsKey(translator.getName())) {
                    throw new IllegalArgumentException(Bundle.FFM_translator_already_exists(providingComponent.getName(), translator.getName()));
                }
                formulaTranslators.put(translator.getName(), translator);
            }
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Package Private Implementation Specifics">
    @Override
    public void initialise() {
    }

    @Override
    public void onAfterComponentsLoaded() {
        // Register all available formula formats and translations:
        for (DiabelliComponent diabelliComponent : diabelli.getRegisteredComponents()) {
            if (diabelliComponent instanceof FormulaFormatsProvider) {
                FormulaFormatsProvider formulaFormatProvider = (FormulaFormatsProvider) diabelliComponent;
                registerFormulaFormats(formulaFormatProvider.getFormulaFormats(), formulaFormatProvider);
            }
            if (diabelliComponent instanceof FormulaTranslationsProvider) {
                FormulaTranslationsProvider ftp = (FormulaTranslationsProvider) diabelliComponent;
                registerFormulaTranslators(ftp.getFormulaTranslators(), ftp);
            }
        }
    }
    // </editor-fold>
}
