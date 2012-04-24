/*
 * File name: TermsToDiabelli.java
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

import diabelli.isabelle.pure.lib.TermUtils;
import diabelli.logic.Formula;
import diabelli.logic.FormulaRepresentation;
import diabelli.logic.Goal;
import isabelle.Term;
import java.util.ArrayList;
import java.util.Collection;
import org.openide.util.NbBundle;

/**
 * Contains method that convert {@link isabelle.Term Isabelle terms} to {@link
 * Goal Diabelli goals}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class TermsToDiabelli {

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    private TermsToDiabelli() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Takes an Isabelle term, extracts premises and conclusions from it, and
     * puts them into a Diabelli goal.
     *
     * @param term well, the term to make into a goal.
     * @return a Diabelli goal (with the extracted premises and conclusions.
     */
    @NbBundle.Messages({
        "TTDG_term_null=Cannot convert a null term into a goal."
    })
    public static TermGoal toGoal(Term.Term term) {
        if (term == null) {
            throw new IllegalArgumentException(Bundle.TTDG_term_null());
        }
        ArrayList<Term.Term> premises = new ArrayList<>();
        ArrayList<Term.Free> variables = new ArrayList<>();
        Term.Term body = TermUtils.findQuantifiedVarsAndBody(term, variables);
        Term.Term conclusion = TermUtils.findPremisesAndConclusion(body, premises);
        return new TermGoal(variables, premises, conclusion, term);
    }

    /**
     * Takes an Isabelle term and wraps it into a Diabelli formula.
     *
     * @param term the term to wrap.
     * @param role the role of this term in the goal.
     * @return a Diabelli formula (containing the term and a description of the
     * term format).
     */
    public static Formula<Term.Term> toFormula(Term.Term term, Formula.FormulaRole role) {
        return new Formula<>(new FormulaRepresentation<>(term, TermFormatDescriptor.getInstance()), role);
    }

    /**
     * Takes a bunch of Isabelle terms and wraps them into a Diabelli formulae.
     *
     * @param terms the terms to wrap.
     * @param role the role of these terms in the goal.
     * @return a bunch of Diabelli formulae (containing the terms and
     * descriptions of the term format).
     */
    public static ArrayList<Formula<Term.Term>> toFormulae(Collection<Term.Term> terms, Formula.FormulaRole role) {
        if (terms != null) {
            ArrayList<Formula<Term.Term>> formulae = new ArrayList<>();
            for (Term.Term term : terms) {
                formulae.add(toFormula(term, role));
            }
            return formulae;
        } else {
            return null;
        }
    }
    // </editor-fold>
}
