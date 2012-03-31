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

import java.io.IOException;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.reasoning.args.SubDiagramIndexArg;

/**
 * A compound spider diagram connects two applies an operator to one or more
 * spider diagrams. <p>Some of the operators one can use in Speedith:
 * conjunction '∧', disjunction '∨', implication '⇒', equivalence '⇔', and
 * negation '¬'.</p> <p>You can construct new compound spider diagrams via the
 * static methods in
 * {@link SpiderDiagrams}.</p> <p>Instances of this class (and its derived
 * classes) are immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CompoundSpiderDiagram extends SpiderDiagram {

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The identifier of the unary spider diagram in the textual representation
     * of spider diagrams. <p>This value is used in the textual representation
     * of spider diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextUnaryId = "UnarySD";
    /**
     * The identifier of the binary spider diagram in the textual representation
     * of spider diagrams. <p>This value is used in the textual representation
     * of spider diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextBinaryId = "BinarySD";
    /**
     * The identifier of a general n-ary spider diagram in the textual
     * representation of spider diagrams. <p>This value is used in the textual
     * representation of spider diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextNaryId = "NarySD";
    /**
     * The prefix (name) of the attributes specifying the operands to this n-ary
     * spider diagram. <p>This value is used in the textual representation of
     * spider diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextArgAttribute = "arg";
    /**
     * The attribute key name for the binary operation of the binary spider
     * diagram. <p>This value is used in the textual representation of spider
     * diagrams (see {@link SpiderDiagram#toString()}).</p>
     */
    public static final String SDTextOperatorAttribute = "operator";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The operator which to apply on the {@link CompoundSpiderDiagram#getOperands()
     * operands}. <p>See {@link Operator#knownOperatorNames()} for a list of all
     * known operators.</p>
     */
    private Operator operator;
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
     *
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
     *
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
        this.operator = operator;
        this.operands = operands;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the n-ary operator that binds the {@link CompoundSpiderDiagram#getOperands() operands}
     * in this n-ary spider diagram.
     *
     * @return the n-ary operator that binds the {@link CompoundSpiderDiagram#getOperands() operands}
     * in this n-ary spider diagram.
     */
    public Operator getOperator() {
        return operator;
    }

    /**
     * Returns the operands of the {@link CompoundSpiderDiagram#getOperator()
     * operator} in this n-ary spider diagram.
     *
     * @return the operands of the {@link CompoundSpiderDiagram#getOperator()
     * operator} in this n-ary spider diagram.
     */
    public List<SpiderDiagram> getOperands() {
        return Collections.unmodifiableList(operands);
    }

    /**
     * Returns the number of operand in this n-ary spider diagram.
     *
     * @return the number of operand in this n-ary spider diagram.
     */
    public int getOperandCount() {
        return operands.size();
    }

    /**
     * Returns the operand at the given index.
     *
     * @param index the index of the operand to fetch.
     * @return the operand at the given index.
     */
    public SpiderDiagram getOperand(int index) {
        return operands.get(index);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns the spider diagram at the given index. <p>This index indicates
     * the number of appearance (from left to right) of a sub-diagram within
     * this compound diagram.</p> <p>See {@link SubDiagramIndexArg} for more
     * info on the <span style="font-style:italic;">diagram indices</span>.</p>
     *
     * @param index the index of the spider sub-diagram in this compound diagram
     * to return.
     * @return the spider sub-diagram at the given index (as it appears in this
     * compound diagram from left to right).
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
    public boolean isValid() {
        for (SpiderDiagram spiderDiagram : operands) {
            if (!spiderDiagram.isValid()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public SpiderDiagram transform(Transformer t, boolean trackParents) {
        if (t == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "t"));
        }
        return transform(t, this, 0, 0, trackParents ? new LinkedList<CompoundSpiderDiagram>() : null);
    }

    @Override
    public <T> T visit(DiagramVisitor<T> visitor, boolean trackParents) {
        if (visitor == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "visitor"));
        }
        visitor.init(this);
        if (!visitor.isDone()) {
            __visitCompoundSD(visitor, this, 0, 0, trackParents ? new LinkedList<CompoundSpiderDiagram>() : null);
        }
        visitor.end();
        return visitor.getResult();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Iterable Implementation">
    public Iterator<SpiderDiagram> iterator() {
        return new CompoundSpiderDiagramIterator(this);
    }

    private static class CompoundSpiderDiagramIterator implements Iterator<SpiderDiagram> {

        private ArrayList<CompoundSDIterationCursor> iterationStack;

        public CompoundSpiderDiagramIterator(CompoundSpiderDiagram csdToIterateThrough) {
            if (csdToIterateThrough == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "csdToIterateThrough"));
            }
            iterationStack = new ArrayList<CompoundSDIterationCursor>();
            iterationStack.add(new CompoundSDIterationCursor(csdToIterateThrough, -1));
        }

        public boolean hasNext() {
            // If there are no unfinished cursors on the stack then there is
            // nothing left to iterate over.
            return getLatestUnfinishedCursor() != null;
        }

        /**
         * Returns the latest cursor that has not passed beyond the operand
         * count of its compound spider diagram (i.e. that points to an existing
         * operand in the compound spider diagram). This method pops all
         * finished cursors from the stack.
         *
         * @return
         */
        private CompoundSDIterationCursor getLatestUnfinishedCursor() {
            // Check first whether there are any cursors at all.
            int lastIndex = iterationStack.size() - 1;
            if (lastIndex < 0) {
                return null;
            }
            // Now peek at the latest cursor and check whether it points to a valid
            // operand.
            CompoundSDIterationCursor cur = iterationStack.get(lastIndex);
            // Check whether the current cursor went past the last operand.
            while (cur.nextChildIndex >= cur.csd.getOperandCount()) {
                // It went past all the operands. We can remove this cursor and
                // move to the next one.
                iterationStack.remove(lastIndex);
                if (--lastIndex >= 0) {
                    cur = iterationStack.get(lastIndex);
                } else {
                    // No cursors left... Return null to indicate that there is
                    // nothing left to visit.
                    return null;
                }
            }
            return cur;
        }

        public SpiderDiagram next() {
            CompoundSDIterationCursor nextCur = getLatestUnfinishedCursor();
            if (nextCur == null) {
                throw new NoSuchElementException();
            }
            SpiderDiagram next;
            if (nextCur.nextChildIndex < 0) {
                next = nextCur.csd;
            } else {
                next = nextCur.csd.getOperand(nextCur.nextChildIndex);
                if (next instanceof CompoundSpiderDiagram) {
                    iterationStack.add(new CompoundSDIterationCursor((CompoundSpiderDiagram) next, 0));
                }
            }
            ++nextCur.nextChildIndex;
            return next;
        }

        public void remove() {
            throw new UnsupportedOperationException(i18n("SD_ITER_REMOVE_NOT_SUPPORTED"));
        }
    }

    private static class CompoundSDIterationCursor {

        final CompoundSpiderDiagram csd;
        int nextChildIndex;

        public CompoundSDIterationCursor(CompoundSpiderDiagram csd, int nextChildIndex) {
            this.csd = csd;
            this.nextChildIndex = nextChildIndex;
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
    public boolean equalsSemantically(SpiderDiagram other) {
        if (equals(other)) {
            return true;
        }
        // 1.) We know that this diagram will equal to another compound spider
        // diagram if they have the same operator and semantically equivalent
        // operands:
        if (other instanceof CompoundSpiderDiagram) {
            CompoundSpiderDiagram csd = (CompoundSpiderDiagram) other;
            boolean operandsSame = operandsSemanticallyEquivalent(csd);
            if (operandsSame && operator.equals(csd.operator)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public int hashCode() {
        if (hashInvalid) {
            hash = operator.hashCode();
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
    public void toString(Appendable sb) throws IOException {
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

    private void printId(Appendable sb) throws IOException {
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

    private void printArg(Appendable sb, int i) throws IOException {
        sb.append(SDTextArgAttribute).append(Integer.toString(i)).append(" = ");
        operands.get(i - 1).toString(sb);
    }

    private void printOperator(Appendable sb) throws IOException {
        sb.append(SDTextOperatorAttribute).append(" = ");
        printString(sb, operator.getName());
    }

    private void printArgs(Appendable sb) throws IOException {
        if (operands.size() > 0) {
            printArg(sb, 1);
            for (int i = 2; i <= operands.size(); i++) {
                printArg(sb.append(", "), i);
            }
        }
    }

    @Override
    public String toString() {
        try {
            final StringBuilder sb = new StringBuilder();
            toString(sb);
            return sb.toString();
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    /**
     * Compares the other non-{@ null} {@link CompoundSpiderDiagram} to this one
     * and returns {@code true} iff they share the same operand and the same
     * operators.
     *
     * @param other
     * @return
     */
    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private boolean __isCsdEqual(CompoundSpiderDiagram other) {
        return hashCode() == other.hashCode()
                && getOperator().equals(other.getOperator())
                && operands.equals(other.operands);
    }

    @SuppressWarnings("AccessingNonPublicFieldOfAnotherObject")
    private static SpiderDiagram transform(Transformer t, CompoundSpiderDiagram curSD, int subDiagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
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
            pushParent(parents, curSD);
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
            popParent(parents);
            // Did any of the children change? If none changed, we must return
            // the unchanged diagram. But if at least one changed, we have to
            // create a new one.
            return transformedChildren == null ? curSD : SpiderDiagrams.createCompoundSD(curSD.getOperator(), transformedChildren, false);
        }
    }

    /**
     * Applies the transformer on the given spider diagram based on the type of
     * the spider diagram.
     *
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

    /**
     * Applies the visit function of the visitor on the given spider diagram.
     * This method returns {@code true} if and only if the visitor is done and
     * no further calls to visit must be made.
     *
     * @param curSD
     * @param visitor
     * @param subDiagramIndex
     * @param childIndex
     * @param parents
     * @return
     */
    private static <T> boolean __visitCompoundSD(DiagramVisitor<T> visitor, CompoundSpiderDiagram curSD, int subDiagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
        // Visit the current spider diagram.
        visitor.visit(curSD, subDiagramIndex++, childIndex, parents);

        // Now visit the child spider diagrams, if it is not finished yet
        // and if there are actually any child spider diagrams.
        if (curSD.getOperandCount() > 0 && !visitor.isDone()) {
            pushParent(parents, curSD);

            // Visit all the children.
            for (childIndex = 0; childIndex < curSD.operands.size(); ++childIndex) {
                SpiderDiagram childSD = curSD.operands.get(childIndex);
                int subDiagramCount = childSD.getSubDiagramCount();
                // Apply the visitor to the current spider diagram and return
                // if it's finished.
                if (__visitSD(childSD, visitor, subDiagramIndex, childIndex, parents)) {
                    return true;
                }
                // When continuing to the next child, we have to increase its
                // sub diagram index by the number of sub-diagrams in the
                // previous child. The child index, however, is incremented by
                // one only (naturally).
                subDiagramIndex += subDiagramCount;
            }
            popParent(parents);
        }
        return visitor.isDone();
    }

    /**
     * Applies the visit function of the visitor on the given spider diagram.
     * This method returns {@code true} if and only if the visitor is done and
     * no further calls to visit must be made.
     *
     * @param sd
     * @param visitor
     * @param subDiagramIndex
     * @param childIndex
     * @param parents
     * @return
     */
    private static <T> boolean __visitSD(SpiderDiagram sd, DiagramVisitor<T> visitor, int subDiagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
        if (sd instanceof CompoundSpiderDiagram) {
            return __visitCompoundSD(visitor, (CompoundSpiderDiagram) sd, subDiagramIndex, childIndex, parents);
        } else {
            visitor.visit(sd, subDiagramIndex, childIndex, parents);
            return visitor.isDone();
        }
    }

    /**
     * Compares the operands of this and the other compound diagram. <p>This
     * method returns {@code true} iff they have the same number of operands and
     * if the operands at the same indices are semantically equivalent.</p>
     *
     * @param other
     * @return
     */
    private boolean operandsSemanticallyEquivalent(CompoundSpiderDiagram other) {
        Iterator<SpiderDiagram> itThis = operands.iterator();
        Iterator<SpiderDiagram> itOther = other.operands.iterator();
        // Firstly, the operands have to be equally many.
        if (operands.size() == other.operands.size()) {
            while (itThis.hasNext()) {
                if (!itThis.next().equalsSemantically(itOther.next())) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    private static void popParent(LinkedList<CompoundSpiderDiagram> parents) {
        // We have finished traversing the children of the current compound
        // diagram. Remove it from the stack of parents.
        if (parents != null) {
            parents.pop();
        }
    }

    private static void pushParent(LinkedList<CompoundSpiderDiagram> parents, CompoundSpiderDiagram curSD) {
        // If we want to process the children of the current SD, make
        // this one the bottom-most parent.
        if (parents != null) {
            parents.push(curSD);
        }
    }
    // </editor-fold>
}
