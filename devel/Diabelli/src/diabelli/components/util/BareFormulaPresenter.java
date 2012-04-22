/*
 * File name: BareFormulaPresenter.java
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
package diabelli.components.util;

import diabelli.components.FormulaPresenter;
import diabelli.logic.Formula;
import diabelli.logic.FormulaFormat;
import diabelli.logic.FormulaRepresentation;
import diabelli.logic.Goal;

/**
 * Provides a basic partial implementation of the {@link FormulaPresenter formula presenter
 * interface}. This class provides implementations of some methods which can be
 * implemented through using others.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class BareFormulaPresenter implements FormulaPresenter {

    @Override
    public boolean canPresent(Goal goal) {
        if (goal == null) {
            return false;
        }
        return canPresent(goal.asFormula());
    }

    @Override
    public boolean canPresent(Formula formula) {
        if (formula == null) {
            return false;
        }
        for (FormulaFormat formulaFormat : formula.getFormats()) {
            if (canPresent(formulaFormat)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean canPresent(FormulaRepresentation<?> formula) {
        if (formula == null) {
            return false;
        }
        return canPresent(formula.getFormat());
    }
}
