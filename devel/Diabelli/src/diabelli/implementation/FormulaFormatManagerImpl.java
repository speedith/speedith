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

/**
 * Diabelli's main implementation of the {@link FormulaFormatManager}.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
class FormulaFormatManagerImpl implements FormulaFormatManager {
    private final Diabelli diabelli;

    public FormulaFormatManagerImpl(Diabelli diabelli) {
        if (diabelli == null) {
            throw new IllegalArgumentException(Bundle.Manager_diabelli_null());
        }
        this.diabelli = diabelli;
    }
    
    // TODO: Add methods for registering new formats, listing all of them, and
    // getting them.
    
    // <editor-fold defaultstate="collapsed" desc="Package Private Implementation Specifics">
    /**
     * This method is called by {@link DiabelliImpl} just after all managers
     * have been constructed. There is no particular order in which Diabelli's
     * managers will have their <pre>initialise()</pre> method called.
     */
    void initialise() {
        
    }
    // </editor-fold>
}
