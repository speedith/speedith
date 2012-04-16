/*
 * File name: FormulaTranslationsProvider.java
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
package diabelli.components;

import diabelli.logic.FormulaTranslator;
import java.util.Collection;

/**
 * Diabelli components of this type can register their formula translators with
 * the {@link FormulaFormatManager formula format manager} (see {@link Diabelli#getFormulaFormatManager()
 * }). The registration process is automatic and happens during Diabelli's
 * loading stage.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface FormulaTranslationsProvider extends DiabelliComponent {

    /**
     * Returns a list of formula translators provided by this Diabelli
     * component.
     *
     * @return a list of formula translators provided by this Diabelli
     * component.
     */
    Collection<FormulaTranslator> getFormulaTranslators();
}
