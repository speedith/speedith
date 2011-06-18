/*
 *   Project: Speedith.Core
 * 
 * File name: CompoundSpiderDiagram.java
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

import java.util.List;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import static speedith.core.i18n.Translations.i18n;

/**
 * A compound spider diagram connects two applies an operator to one or more
 * spider diagrams.
 * <p>Some of the operators one can use in Speedith: conjunction '∧',
 * disjunction '∨', implication '⇒', equivalence '⇔', and negation '¬'.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CompoundSpiderDiagram extends SpiderDiagram {

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The identifier of the unary spider diagram in the textual representation
     * of spider diagrams.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextUnaryId = "UnarySD";
    /**
     * The identifier of the binary spider diagram in the textual representation
     * of spider diagrams.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextBinaryId = "BinarySD";
    /**
     * The identifier of a general n-ary spider diagram in the textual representation
     * of spider diagrams.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextNaryId = "NarySD";
    /**
     * The prefix (name) of the attributes specifying the operands to this n-ary
     * spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextArgAttribute = "arg";
    /**
     * The attribute key name for the binary operation of the binary spider diagram.
     * <p>This value is used in the textual representation of spider diagrams
     * (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextOperatorAttribute = "operator";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The operator which to apply on the {@link CompoundSpiderDiagram#getOperands()
     * operands}.
     * <p>See {@link Operator#knownOperatorNames()} for a list of all known
     * operators.</p>
     */
    private Operator operator;
    /**
     * A list of operands taken by the {@link CompoundSpiderDiagram#getOperator()
     * operator}.
     */
    private ArrayList<SpiderDiagram> operands;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises a new n-ary spider diagram.
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     */
    public CompoundSpiderDiagram(String operator, Collection<SpiderDiagram> operands) {
        this.operator = Operator.fromString(operator);
        if (this.operator == null) {
            throw new IllegalArgumentException(i18n("ERR_OPERATOR_NOT_KNOWN", operator));
        }
        if (operands == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "operands"));
        }
        if (operands.size() != this.operator.getArity()) {
            throw new IllegalArgumentException(i18n("ERR_WRONG_NUMBER_OF_OPERANDS", this.operator.getName(), this.operator.getArity(), operands.size()));
        }
        for (SpiderDiagram spiderDiagram : operands) {
            if (spiderDiagram == null) {
                throw new IllegalArgumentException(i18n("ERR_OPERAND_NULL"));
            }
        }
        this.operands = new ArrayList<SpiderDiagram>(operands);
    }

    /**
     * Initialises the nary-spider diagram with the given operator and operands.
     * <p><span style="font-weight:bold">Note</span>: this constructor does not
     * make a copy of the given array list. Take heed on how you use it.</p>
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     */
    CompoundSpiderDiagram(Operator operator, ArrayList<SpiderDiagram> operands) {
        if (operator == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "operator"));
        }
        if (operands == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "operands"));
        }
        if (operands.size() != operator.getArity()) {
            throw new IllegalArgumentException(i18n("ERR_WRONG_NUMBER_OF_OPERANDS", operator, operator.getArity(), operands.size()));
        }
        this.operator = operator;
        this.operands = operands;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the n-ary operator that binds the {@link CompoundSpiderDiagram#getOperands() operands}
     * in this n-ary spider diagram.
     * @return the n-ary operator that binds the {@link CompoundSpiderDiagram#getOperands() operands}
     * in this n-ary spider diagram.
     */
    public Operator getOperator() {
        return operator;
    }

    /**
     * Returns the operands of the {@link CompoundSpiderDiagram#getOperator()
     * operator} in this n-ary spider diagram.
     * @return the operands of the {@link CompoundSpiderDiagram#getOperator()
     * operator} in this n-ary spider diagram.
     */
    public List<SpiderDiagram> getOperands() {
        return Collections.unmodifiableList(operands);
    }

    /**
     * Returns the number of operand in this n-ary spider diagram.
     * @return the number of operand in this n-ary spider diagram.
     */
    public int getOperandCount() {
        return operands.size();
    }

    /**
     * Returns the operand at the given index.
     * @param index the index of the operand to fetch.
     * @return the operand at the given index.
     */
    public SpiderDiagram getOperand(int index) {
        return operands.get(index);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Equality">
    @Override
    public boolean equals(SpiderDiagram other) {
        if (other == this) {
            return true;
        } else if (other instanceof CompoundSpiderDiagram) {
            return __isNsdEqual((CompoundSpiderDiagram) other);
        } else {
            return false;
        }
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        } else if (other instanceof CompoundSpiderDiagram) {
            return __isNsdEqual((CompoundSpiderDiagram) other);
        } else {
            return false;
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Text Conversion Methods">
    @Override
    public void toString(StringBuilder sb) {
        if (sb == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "sb"));
        }
        printId(sb);
        sb.append(" {");
        printOperator(sb);
        sb.append(", ");
        printArgs(sb);
        sb.append('}');
    }

    private void printId(StringBuilder sb) {
        switch (getOperandCount()) {
            case 1:
                sb.append(SDTextUnaryId);
                break;
            case 2:
                sb.append(SDTextBinaryId);
                break;
            default:
                sb.append(SDTextNaryId);
                break;
        }
    }

    private void printArg(StringBuilder sb, int i) {
        sb.append(SDTextArgAttribute).append(i).append(" = ");
        operands.get(i - 1).toString(sb);
    }

    private void printOperator(StringBuilder sb) {
        sb.append(SDTextOperatorAttribute).append(" = ");
        printString(sb, operator.getName());
    }

    private void printArgs(StringBuilder sb) {
        if (operands.size() > 0) {
            printArg(sb, 1);
            for (int i = 2; i <= operands.size(); i++) {
                printArg(sb.append(", "), i);
            }
        }
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        toString(sb);
        return sb.toString();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    /**
     * Compares the other non-{@ null} {@link CompoundSpiderDiagram} to this one and
     * returns {@code true} iff they share the same operand and the same
     * operators.
     * @param other
     * @return 
     */
    private boolean __isNsdEqual(CompoundSpiderDiagram other) {
        return getOperator().equals(other.getOperator())
                && operands.equals(other.operands);
    }
    // </editor-fold>
}
