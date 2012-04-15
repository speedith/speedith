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
import java.util.*;
import org.openide.util.NbBundle;

/**
 * Represents a general formula. It can be a diagrammatic, sentential, or both
 * at the same time (if the {@link GoalProvidingReasoner reasoner} provides more
 * than one representation of this formula). This class can thus carry many
 * representations, or formats, of the same formula. For example, a formula can
 * be represented with many strings (using syntaxes of many theorem provers),
 * with term trees (abstract syntax trees), or similar. However, there is always
 * {@link Formula#getMainRepresentation() one main representation}. Other
 * representations should be equivalent to it, or at least have the proper
 * logical relation to it (i.e., if this formula is {@link Goal#getPremises() a
 * premise}, then all other representations of it must be logically entailed by
 * the {@link Formula#getMainRepresentation() main representation}; on the other
 * hand, when the formula is {@link Goal#getConclusion() a conclusion}, then the
 * other direction of entailment must hold; the representations can be logically
 * equivalent, i.e., mutually entailed, which is always allowed).
 *
 * <p><span style="font-weight:bold">Note</span>: a formula may have only one
 * representation in a particular {@link FormulaFormatDescriptor format}.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@NbBundle.Messages({
    "Formula_null_main_representation=The formula must have a main representation."
})
public class Formula {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final FormulaRepresentation<?> mainRepresentation;
    private final HashMap<String, FormulaRepresentation<?>> representations;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a formula with the given list of different representations.
     *
     * @param mainRepresentation the main representation of this formula.
     * <p>Other representations must be either entailed by this representation
     * (if this formula acts as a premise) or they must entail the main
     * representation (if this formula acts as a conclusion).</p>
     * @param otherRepresentations this list of representations must contain at
     * least one element. The first element of the list will become the {@link
     * Formula#getMainRepresentation() main representation}.
     */
    public Formula(FormulaRepresentation<?> mainRepresentation, Collection<FormulaRepresentation<?>> otherRepresentations) {
        if (mainRepresentation == null) {
            throw new IllegalArgumentException(Bundle.Formula_null_main_representation());
        }
        this.mainRepresentation = mainRepresentation;
        this.representations = new HashMap<String, FormulaRepresentation<?>>();
        this.representations.put(mainRepresentation.getFormat().getFormatName(), mainRepresentation);
        if (otherRepresentations != null) {
            for (FormulaRepresentation<?> formulaRepresentation : otherRepresentations) {
                this.representations.put(formulaRepresentation.getFormat().getFormatName(), formulaRepresentation);
            }
        }
    }

    /**
     * Creates a formula with the given list of different representations.
     *
     * @param mainRepresentation the main representation of this formula.
     * <p>Other representations must be either entailed by this representation
     * (if this formula acts as a premise) or they must entail the main
     * representation (if this formula acts as a conclusion).</p>
     * @param otherRepresentations this list of representations must contain at
     * least one element. The first element of the list will become the {@link
     * Formula#getMainRepresentation() main representation}.
     */
    public Formula(FormulaRepresentation<?> mainRepresentation, FormulaRepresentation<?>... otherRepresentations) {
        this(mainRepresentation, otherRepresentations == null || otherRepresentations.length < 1 ? null : Arrays.asList(otherRepresentations));
    }

    /**
     * Creates a formula with the given list of different representations.
     *
     * @param mainRepresentation the main representation of this formula.
     * <p>Other representations must be either entailed by this representation
     * (if this formula acts as a premise) or they must entail the main
     * representation (if this formula acts as a conclusion).</p>
     * @param otherRepresentations this list of representations must contain at
     * least one element. The first element of the list will become the {@link
     * Formula#getMainRepresentation() main representation}.
     */
    public Formula(FormulaRepresentation<?> mainRepresentation, ArrayList<FormulaRepresentation<?>> otherRepresentations) {
        this(mainRepresentation, (Collection<FormulaRepresentation<?>>) otherRepresentations);
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the main representation of this formula. This is usually the
     * native formula representation of the {@link GoalProvidingReasoner
     * reasoner} that provided this formula.
     *
     * <p>Other representations must be either entailed by this representation
     * (if this formula acts as a premise) or they must entail the main
     * representation (if this formula acts as a conclusion).</p>
     *
     * @return the main representation of this formula.
     */
    public FormulaRepresentation<?> getMainRepresentation() {
        return mainRepresentation;
    }

    /**
     * Returns all representations of this formula. This collection includes the
     * main representation (as the first element).
     *
     * @return all representations of this formula.
     */
    public Collection<FormulaRepresentation<?>> getRepresentations() {
        // We synchronise here because we may add new representations in another
        // thread.
        synchronized (representations) {
            return Collections.unmodifiableCollection(representations.values());
        }
    }

    /**
     * Returns the number of representations this formula has. The minimum this
     * function can return is {@code 1}.
     *
     * @return the number of representations this formula has.
     */
    public int getRepresentationsCount() {
        synchronized (representations) {
            return representations.size();
        }
    }

    /**
     * Returns the representation of this formula in the given format. This
     * method does not try to convert the formula into the given format.
     *
     * @param format
     * @return
     */
    public FormulaRepresentation<?> getRepresentation(FormulaFormatDescriptor format) {
        synchronized (representations) {
            return representations.get(format.getFormatName());
        }
    }
    // </editor-fold>
}
