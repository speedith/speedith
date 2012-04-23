/*
 * File name: TermFormatDescriptor.java
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
package diabelli.isabelle.terms;

import diabelli.logic.FormulaFormatDescriptor;
import isabelle.Term;
import org.openide.util.NbBundle;

/**
 * The formula format descriptor for Isabelle formulae in the term form.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@NbBundle.Messages({
    "TFD_term_format_pretty_name=Isabelle term"
})
public class TermFormatDescriptor extends FormulaFormatDescriptor<Term.Term> {
    
    //<editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of Isabelle's term tree format. This name is used in {@link FormulaFormatDescriptor#getFormatName()}.
     */
    public static final String TermFormatName = "Isabelle_term_tree";
    //</editor-fold>
    
    //<editor-fold defaultstate="collapsed" desc="Constructor">
    private TermFormatDescriptor() {
        super(TermFormatName, Bundle.TFD_term_format_pretty_name(), isabelle.Term.Term.class);
    }
    //</editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Singleton Instance">
    /**
     * Returns the singleton instance of the Isabelle term format descriptor.
     * @return the singleton instance of the Isabelle term format descriptor.
     */
    public static TermFormatDescriptor getInstance() {
        return SingletonContainer.Instance;
    }

    private static class SingletonContainer {
        
        private static final TermFormatDescriptor Instance = new TermFormatDescriptor();
        
    }
    // </editor-fold>
}
