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
import diabelli.components.FormulaFormatProvider;
import diabelli.components.GoalProvidingReasoner;
import diabelli.logic.FormulaFormatDescriptor;
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
    private final Diabelli diabelli;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    FormulaFormatManagerImpl(Diabelli diabelli) {
        if (diabelli == null) {
            throw new IllegalArgumentException(Bundle.Manager_diabelli_null());
        }
        this.diabelli = diabelli;
        this.formulaFormats = new HashMap<String, FormulaFormatDescriptor>();
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
    void registerFormulaFormats(Collection<FormulaFormatDescriptor> formats, FormulaFormatProvider providingComponent) {
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
        // Register all available formula formats:
        for (DiabelliComponent diabelliComponent : diabelli.getRegisteredComponents()) {
            if (diabelliComponent instanceof FormulaFormatProvider) {
                FormulaFormatProvider formulaFormatProvider = (FormulaFormatProvider) diabelliComponent;
                registerFormulaFormats(formulaFormatProvider.getFormulaFormats(), formulaFormatProvider);
            }
        }
    }
    // </editor-fold>
}
