/*
 * File name: FormulaFormatManager.java
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
package diabelli;

import diabelli.components.DiabelliComponent;
import diabelli.logic.FormulaFormatDescriptor;
import diabelli.logic.FormulaRepresentation;
import diabelli.logic.FormulaTranslator;
import java.util.ArrayList;
import java.util.Collection;
import org.netbeans.api.annotations.common.NonNull;

/**
 * Provides a central mechanism for registering known {@link
 * FormulaFormatDescriptor formula formats}. This provides a way for
 * identifying, translating, and understanding of {@link FormulaRepresentation formulae}
 * in different formats. Since Diabelli's main goal is to connect different
 * reasoners, all of which may understand different representations, this class
 * provides a solution for ease of translation between the reasoners.
 * <p>Formula formats are registered when {@link DiabelliComponent Diabelli components}
 * are loaded. The components which want to register new formula formats must 
 * implement the {@link FormulaFormatProvider} interface.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface FormulaFormatManager {

    /**
     * Returns all registered formula formats.
     * @return all registered formula formats.
     */
    @NonNull
    Collection<FormulaFormatDescriptor> getFormulaFormats();

    /**
     * Returns all registered formula translators.
     * @return all registered formula translators.
     */
    @NonNull
    Collection<FormulaTranslator> getFormulaTranslators();
    
}
