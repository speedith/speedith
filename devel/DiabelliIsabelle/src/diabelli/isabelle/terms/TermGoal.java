/*
 * File name: TermGoal.java
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

import diabelli.logic.Formula;
import diabelli.logic.Goal;
import isabelle.Term.Free;
import isabelle.Term.Term;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A Diabelli goal in the form of Isabelle terms.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class TermGoal extends Goal {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    private final ArrayList<Free> variables;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructor">
    TermGoal(ArrayList<Free> variables, ArrayList<Term> premises, Term conclusion, Term term) {
        super(TermsToDiabelli.toFormulae(premises, Formula.FormulaRole.Premise),
                TermsToDiabelli.toFormula(conclusion, Formula.FormulaRole.Conclusion),
                TermsToDiabelli.toFormula(term, Formula.FormulaRole.Goal));
        this.variables = variables;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Contains a list of globally meta-quantified variables. These variables
     * are referenced from the {@link Goal#asFormula() body} as bound variables
     * (where the binding index 0 references the last variable in the list).
     * When the formula is passed back to Isabelle, these quantified variables
     * should be put back into the top of the term.
     *
     * <p><span style="font-weight:bold">Note</span>: this method will return {@code null}
     * to indicate that there are no globally meta-quantified variables in this
     * goal.</p>
     *
     * @return a list of globally meta-quantified variables.
     */
    public List<Free> getVariables() {
        return variables == null || variables.isEmpty() ? null : Collections.unmodifiableList(variables);
    }

    /**
     * Returns the number of {@link TermGoal#getVariables() globally
     * meta-quantified variables} in this goal.
     *
     * @return the number of {@link TermGoal#getVariables() globally
     * meta-quantified variables} in this goal.
     */
    public int getVariablesCount() {
        return variables == null ? 0 : variables.size();
    }
    //</editor-fold>
}
