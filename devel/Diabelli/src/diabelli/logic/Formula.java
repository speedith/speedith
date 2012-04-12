/*
 * File name: Formula.java
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

import diabelli.components.GoalProvidingReasoner;
import java.util.List;

/**
 * Represents a general formula. It can be a diagrammatic, sentential, or both
 * at the same time (if the {@link GoalProvidingReasoner reasoner} provides more
 * than one representation of this formula). This class can thus carry many
 * representations, or formats, of the same formula. For example, a formula
 * can be represented with many strings (using syntaxes of many theorem provers),
 * with term trees (abstract syntax trees), or similar. However, there is always
 * {@link Formula#getMainRepresentation() one main representation}. Other
 * representations should be equivalent to it, or at least have the proper
 * logical relation to it (i.e., if this formula is {@link Goal#getPremises() a
 * premise}, then all other representations of it must be logically entailed by
 * the {@link Formula#getMainRepresentation() main representation}; on the other
 * hand, when the formula is {@link Goal#getConclusion() a conclusion}, then the
 * other direction of entailment must hold; the representations can be
 * logically equivalent, i.e., mutually entailed, which is always allowed).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Formula {
    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the main representation of this formula. This is usually the
     * native formula representation of the {@link GoalProvidingReasoner
     * reasoner} that provided this formula.
     * @return the main representation of this formula.
     */
    public FormulaRepresentation getMainRepresentation() {
        return null;
    }
    
    /**
     * Returns all representations of this formula. This list includes the main
     * representation.
     * @return all representations of this formula.
     */
    public List<FormulaRepresentation> getRepresentations() {
        return null;
    }
    // </editor-fold>
}
