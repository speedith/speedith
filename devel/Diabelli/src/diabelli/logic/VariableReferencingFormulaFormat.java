/*
 * File name: VariableReferencingFormulaFormat.java
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

import java.util.Set;

/**
 * Formulae of this format may contain free variables (or variables that are
 * bound outside of the scope of the formula).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface VariableReferencingFormulaFormat extends FormulaFormat {
    /**
     * Returns the names of variables that are free in the formula (or that are
     * bound outside of the scope of the formula). The context goal may be used
     * to determine the names of globally bound variables.
     * @param formula the formula from which we want to extract free variables.
     * @param context the context which the variable extraction algorithm may
     * use to find the proper names.
     * @return the names of variables that are free in the formula (or that are
     * bound outside of the scope of the formula).
     */
    Set<String> getFreeVariables(Formula formula, Goal context);
}
