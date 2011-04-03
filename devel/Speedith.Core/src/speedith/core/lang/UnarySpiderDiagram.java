/*
 *   Project: Speedith.Core
 * 
 * File name: UnarySpiderDiagram.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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

package speedith.core.lang;

import static speedith.core.i18n.Translations.i18n;

/**
 * A compound spider diagram that applies one spider diagram to a unary
 * operator (e.g.: negation '¬').
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class UnarySpiderDiagram extends SpiderDiagram {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The unary operator used in this unitary spider diagram (e.g.: negation
     * '¬').
     */
    private String operator;
    /**
     * This is the operand of the unary operation.
     */
    private SpiderDiagram operand;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises a new unary spider diagram.
     * @param operator the {@link UnarySpiderDiagram#getOperator() unary
     * operator} that operates over the single
     * {@link UnarySpiderDiagram#getOperand() operand} of this unary spider
     * diagram.
     * @param operand the {@link UnarySpiderDiagram#getOperand() operand}
     * to the {@link UnarySpiderDiagram#getOperator() unary operator}.
     */
    public UnarySpiderDiagram(String operator, SpiderDiagram operand) {
        this.operator = operator;
        this.operand = operand;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the unary operator that binds the {@link UnarySpiderDiagram#getOperand() operand}
     * in this unary spider diagram.
     * @return the unary operator that binds the {@link UnarySpiderDiagram#getOperand() operand}
     * in this unary spider diagram.
     */
    public String getOperator() {
        return operator;
    }

    /**
     * Returns the only operand of the {@link UnarySpiderDiagram#getOperator()
     * unary operator} in this unary spider diagram.
     * @return the only operand of the {@link UnarySpiderDiagram#getOperator()
     * unary operator} in this unary spider diagram.
     */
    public SpiderDiagram getOperand() {
        return operand;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    @Override
    public void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
    }
    // </editor-fold>
}
