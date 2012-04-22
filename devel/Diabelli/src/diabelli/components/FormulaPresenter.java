/*
 * File name: FormulaPresenter.java
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

import diabelli.logic.Formula;
import diabelli.logic.FormulaFormat;
import diabelli.logic.FormulaRepresentation;
import diabelli.logic.Goal;
import diabelli.ui.CurrentFormulaTopComponent;
import javax.swing.JPanel;

/**
 * Formula presenters take a {@link Formula Diabelli formula} and return a
 * visual component that displays the formula. For example, a formula with a
 * spider-diagrammatic {@link Formula#getRepresentations(diabelli.logic.FormulaFormatDescriptor) representation}
 * could be visualised with a spider diagram. Diabelli components (like
 * Speedith for Diabelli) provides visual representations through this
 * interface.
 *
 * <p>The user selects the formula to be represented through the user interface.
 * Specifically, {@link CurrentFormulaTopComponent} is responsible for selecting
 * the formula that should be displayed with the help of presenters.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface FormulaPresenter extends DiabelliComponent {
    
    /**
     * Should return {@code true} if this presenter can produce a visualisation
     * of the given goal.
     * @param goal the goal about which we are asking this presenter.
     * @return {@code true} if this presenter can produce a visualisation
     * of the given goal.
     */
    boolean canPresent(Goal goal);
    
    /**
     * Should return {@code true} if this presenter can produce a visualisation
     * of the given formula.
     * @param formula the formula about which we are asking this presenter.
     * @return {@code true} if this presenter can produce a visualisation
     * of the given formula.
     */
    boolean canPresent(Formula formula);
    
    /**
     * Should return {@code true} if this presenter can produce a visualisation
     * of the given formula.
     * @param formula the formula about which we are asking this presenter.
     * @return {@code true} if this presenter can produce a visualisation
     * of the given formula.
     */
    boolean canPresent(FormulaRepresentation<?> formula);
    
    /**
     * Should return {@code true} if this presenter can produce a visualisation
     * of formulae in the given format.
     * @param format the format of formulae about which we are asking this presenter.
     * @return {@code true} if this presenter can produce a visualisation
     * of formulae in the given format.
     */
    boolean canPresent(FormulaFormat format);
    
    /**
     * Returns a panel which displays the given goal. The returned panel will
     * be placed in a sub-window in the main GUI of Diabelli.
     * @param formula the formula to be visualised.
     * @return a panel which displays the given goal.
     */
    JPanel createVisualiserFor(Goal formula);
    
    /**
     * Returns a panel which displays the given goal. The returned panel will
     * be placed in a sub-window in the main GUI of Diabelli.
     * @param formula the formula to be visualised.
     * @return a panel which displays the given goal.
     */
    JPanel createVisualiserFor(Formula formula);
    
    /**
     * Returns a panel which displays the given goal. The returned panel will
     * be placed in a sub-window in the main GUI of Diabelli.
     * @param formula the formula to be visualised.
     * @return a panel which displays the given goal.
     */
    JPanel createVisualiserFor(FormulaRepresentation<?> formula);
}
