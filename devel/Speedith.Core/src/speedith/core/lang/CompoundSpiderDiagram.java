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
import java.util.LinkedList;
import speedith.core.reasoning.args.DiagramIndexArg;
import static speedith.core.i18n.Translations.i18n;

/**
 * A compound spider diagram connects two applies an operator to one or more
 * spider diagrams.
 * <p>Some of the operators one can use in Speedith: conjunction '∧',
 * disjunction '∨', implication '⇒', equivalence '⇔', and negation '¬'.</p>
 * <p>You can construct new compound spider diagrams via the static methods in
 * {@link SpiderDiagrams}.</p>
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
    private Operator m_operator;
    /**
     * A list of operands taken by the {@link CompoundSpiderDiagram#getOperator()
     * operator}.
     */
    private ArrayList<SpiderDiagram> operands;
    private boolean hashInvalid = true;
    private int hash;
    private int subDiagramCount = -1;
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
    CompoundSpiderDiagram(String operator, Collection<SpiderDiagram> operands) {
        this(Operator.fromString(operator), operands == null ? null : new ArrayList<SpiderDiagram>(operands));
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
        for (SpiderDiagram spiderDiagram : operands) {
            if (spiderDiagram == null) {
                throw new IllegalArgumentException(i18n("ERR_OPERAND_NULL"));
            }
        }
        this.m_operator = operator;
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
        return m_operator;
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

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns the spider diagram at the given index.
     * <p>This index indicates the number of appearance (from left to right) of
     * a sub-diagram within this compound diagram.</p>
     * <p>See {@link DiagramIndexArg} for more info on the
     * <span style="font-style:italic;">diagram indices</span>.</p>
     * @param index the index of the spider sub-diagram in this compound
     * diagram to return.
     * @return the spider sub-diagram at the given index (as it appears in
     * this compound diagram from left to right).
     */
    @Override
    public SpiderDiagram getSubDiagramAt(int index) {
        if (index == 0) {
            return this;
        } else if (index > 0) {
            --index;
            for (int i = 0; i < operands.size(); i++) {
                SpiderDiagram sub = operands.get(i);
                int subCount = sub.getSubDiagramCount();
                if (subCount > index) {
                    return sub.getSubDiagramAt(index);
                }
                index -= subCount;
            }
        }
        return null;
    }

    @Override
    public int getSubDiagramCount() {
        if (subDiagramCount < 0) {
            subDiagramCount = 1;
            for (int i = 0; i < operands.size(); i++) {
                subDiagramCount += operands.get(i).getSubDiagramCount();
            }
        }
        return subDiagramCount;
    }

    @Override
    public SpiderDiagram transform(Transformer t) {
        if (t == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "t"));
        }
        return transform(t, this, 0, 0, new LinkedList<CompoundSpiderDiagram>());
    }

    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private static SpiderDiagram transform(Transformer t, CompoundSpiderDiagram curSD, int childIndex, int subDiagramIndex, LinkedList<CompoundSpiderDiagram> parents) {
        // Try to transform this sub-diagram.
        SpiderDiagram transformedSD = t.transform(curSD, subDiagramIndex, childIndex, parents);
        // What did the transformer return? Is it done yet?
        if (transformedSD != null) {
            // The transformer either changed the diagram, or it indicated that
            // we should not descend into it. In this case the transformed
            // diagram has to be returned.
            return transformedSD;
        } else if (t.isDone()) {
            // The transformer doesn't want to do anything anymore and the
            // transformed diagram is null. So, we have to return the unchanged
            // spider diagram.
            return curSD;
        } else {
            // The transformer didn't change the current diagram AND it wants us
            // to descend down it.
            // So, let's do it. Call the transformer on the children of this
            // compound diagram. If at least one child changed, create a new
            // compound spider diagram and return it.

            // If we want to process the children of the current SD, make it the
            // last parent.
            parents.push(curSD);
            // This array will hold the children (if at least one of them was
            // transformed).
            ArrayList<SpiderDiagram> transformedChildren = null;
            // Now traverse all the children:
            for (childIndex = 0; childIndex < curSD.operands.size(); ++childIndex) {
                SpiderDiagram childSD = curSD.operands.get(childIndex);
                int subDiagramCount = childSD.getSubDiagramCount();
                // Transform the child
                transformedSD = __applyTransform(childSD, t, subDiagramIndex + 1, childIndex, parents);
                // If the child was actually transformed, put it into the list
                // of transformed children.
                if (transformedSD != null && !transformedSD.equals(childSD)) {
                    if (transformedChildren == null) {
                        transformedChildren = new ArrayList<SpiderDiagram>(curSD.operands);
                    }
                    transformedChildren.set(childIndex, transformedSD);
                }
                // If the transformed indicates it's finished. Stop the
                // traversal.
                if (t.isDone()) {
                    break;
                }
                // When continuing to the next child, we have to increase its
                // sub diagram index by the number of sub-diagrams in the
                // previous child. The child index, however, is incremented by
                // one only (naturally).
                subDiagramIndex += subDiagramCount;
            }
            // We have finished traversing the children of the current compound
            // diagram. Remove it from the stack of parents.
            parents.pop();
            // Did any of the children change? If none changed, we must return
            // the unchanged diagram. But if at least one changed, we have to
            // create a new one.
            return transformedChildren == null ? curSD : SpiderDiagrams.createCompoundSD(curSD.getOperator(), transformedChildren, false);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Equality">
    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        } else if (other instanceof CompoundSpiderDiagram) {
            return __isCsdEqual((CompoundSpiderDiagram) other);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = m_operator.hashCode();
            if (operands != null) {
                for (SpiderDiagram sd : operands) {
                    hash += sd.hashCode();
                }
            }
            hashInvalid = false;
        }
        return hash;
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
        printString(sb, m_operator.getName());
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
    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private boolean __isCsdEqual(CompoundSpiderDiagram other) {
        return getOperator().equals(other.getOperator())
                && operands.equals(other.operands);
    }

    /**
     * Applies the transformer on the given spider diagram based on the type of
     * the spider diagram.
     * @param sd
     * @param t
     * @param subDiagramIndex
     * @param childIndex
     * @param parents
     * @return 
     */
    private static SpiderDiagram __applyTransform(SpiderDiagram sd, Transformer t, int subDiagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
        if (sd instanceof CompoundSpiderDiagram) {
            return transform(t, (CompoundSpiderDiagram) sd, subDiagramIndex, childIndex, parents);
        } else if (sd instanceof PrimarySpiderDiagram) {
            return t.transform((PrimarySpiderDiagram) sd, subDiagramIndex, childIndex, parents);
        } else {
            return t.transform((NullSpiderDiagram) sd, subDiagramIndex, childIndex, parents);
        }
    }
    // </editor-fold>
}
