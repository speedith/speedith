/*
 *   Project: Speedith.Core
 * 
 * File name: ProofEx.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
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
package speedith.core.reasoning;

import speedith.core.lang.SpiderDiagram;

/**
 * This class contains the original statement (a {@link SpiderDiagram spider
 * diagram}), a proof trace (a sequence of applied inference rules with
 * intermediate subgoals -- the latter are lists of spider diagrams), indicators
 * of whether the proof is complete or trusted etc.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ProofEx extends ProofTraceEx {

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises a new proof with the given initial goal.
     * @param initialGoals the initial goal (may be {@code null} or empty to
     * indicate a proof without proof obligations -- an empty proof).
     */
    public ProofEx(Goals initialGoals) {
        super(initialGoals);
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    // TODO: Specify the interface.
    // </editor-fold>
}
