/*
 *   Project: Speedith.Core
 * 
 * File name: BinarySpiderDiagram.java
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
package speedith.core.lang;

import static speedith.core.i18n.Translations.i18n;

/**
 * A compound spider diagram connects two spider diagrams with a binary
 * predicate (e.g.: and '∧', or '∨', implication '⇒', equivalence '⇔', etc.).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class BinarySpiderDiagram extends SpiderDiagram {
    
    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The identifier of the binary spider diagram in the textual representation
     * of spider diagrams.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link BinarySpiderDiagram#toString()}).</p>
     */
    public static final String SDTextBinaryId = "BinarySD";
    /**
     * The attribute key name for the first argument (operand) of the binary operation in
     * a binary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link BinarySpiderDiagram#toString()}).</p>
     */
    public static final String SDTextArg1Attribute = "arg1";
    /**
     * The attribute key name for the second argument (operand) of the binary operation in
     * a binary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link BinarySpiderDiagram#toString()}).</p>
     */
    public static final String SDTextArg2Attribute = "arg2";
    /**
     * The attribute key name for the binary operation of the binary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link BinarySpiderDiagram#toString()}).</p>
     */
    public static final String SDTextOperatorAttribute = "operator";
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The connective that binds the left and right operands of this binary
     * spider diagram.
     */
    private String operator;
    /**
     * This is the left operand of the binary operation.
     */
    private SpiderDiagram leftOperand;
    /**
     * This is the right operand of the binary operation.
     */
    private SpiderDiagram rightOperand;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises a new binary spider diagram.
     * @param operator the {@link BinarySpiderDiagram#getOperator() binary
     * operator} that should connect the {@link BinarySpiderDiagram#getLeftOperand() left}
     * and the {@link BinarySpiderDiagram#getRightOperand() right} operands.
     * @param leftOperand the {@link BinarySpiderDiagram#getLeftOperand() left}
     * operand of the {@link BinarySpiderDiagram#getOperator() binary operator}.
     * @param rightOperand the {@link BinarySpiderDiagram#getRightOperand() right}
     * operand of the {@link BinarySpiderDiagram#getOperator() binary operator}.
     */
    public BinarySpiderDiagram(String operator, SpiderDiagram leftOperand, SpiderDiagram rightOperand) {
        this.operator = operator;
        this.leftOperand = leftOperand;
        this.rightOperand = rightOperand;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the binary operator that binds the {@link BinarySpiderDiagram#getLeftOperand() left}
     * and {@link BinarySpiderDiagram#getRightOperand() right} operands in this
     * binary spider diagram.
     * @return the binary operator that binds the {@link BinarySpiderDiagram#getLeftOperand() left}
     * and {@link BinarySpiderDiagram#getRightOperand() right} operands in this
     * binary spider diagram.
     */
    public String getOperator() {
        return operator;
    }

    /**
     * Returns the left operand of the {@link BinarySpiderDiagram#getOperator()
     * binary operator} in this binary spider diagram.
     * @return the left operand of the {@link BinarySpiderDiagram#getOperator()
     * binary operator} in this binary spider diagram.
     */
    public SpiderDiagram getLeftOperand() {
        return leftOperand;
    }

    /**
     * Returns the right operand of the {@link BinarySpiderDiagram#getOperator()
     * binary operator} in this binary spider diagram.
     * @return the right operand of the {@link BinarySpiderDiagram#getOperator()
     * binary operator} in this binary spider diagram.
     */
    public SpiderDiagram getRightOperand() {
        return rightOperand;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    @Override
    public void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        sb.append(SDTextBinaryId);
        sb.append(" {");
        printOperator(sb);
        sb.append(", ");
        printArg1(sb);
        sb.append(", ");
        printArg2(sb);
        sb.append('}');
    }

    private void printOperator(StringBuilder sb) {
        sb.append(SDTextOperatorAttribute).append(" = ");
        printString(sb, operator);
    }

    private void printArg1(StringBuilder sb) {
        sb.append(SDTextArg1Attribute).append(" = ");
        leftOperand.toString(sb);
    }

    private void printArg2(StringBuilder sb) {
        sb.append(SDTextArg2Attribute).append(" = ");
        rightOperand.toString(sb);
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        toString(sb);
        return sb.toString();
    }
    // </editor-fold>
}
