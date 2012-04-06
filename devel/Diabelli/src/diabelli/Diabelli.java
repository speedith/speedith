/*
 * File name: Diabelli.java
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

import org.openide.util.Lookup;
import org.openide.util.lookup.Lookups;

/**
 * This is the main entry point to Diabelli for other I3P plugins. Reasoners can
 * register themselves here, currently opened standalone reasoners (the ones
 * that host a proof) can be found here, supporting reasoners (the ones which
 * can apply inference steps on goals or prove them outright, display goals,
 * provide formula input mechanisms etc.), currently pending goals in a proof of
 * a standalone reasoner etc.
 *
 * <p><span style="font-weight:bold">Note</span>: This class is a singleton,
 * access its only instance through</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Diabelli implements Lookup.Provider {
    
    // <editor-fold defaultstate="collapsed" desc="Constructor">
    private Diabelli() {
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Singleton Stuff">
    /**
     * Returns the only instance of this class.
     * @return the only instance of this class.
     */
    public static Diabelli getInstance() {
        return SingletonContainer.Instance;
    }
    
    /**
     * This class lazily instantiates the Diabelli instance.
     */
    private static final class SingletonContainer {

        private static final Diabelli Instance = new Diabelli();
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Lookup Provider Implementation">
    @Override
    public Lookup getLookup() {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    // </editor-fold>
}
