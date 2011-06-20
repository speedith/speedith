/*
 *   Project: Speedith.Core
 * 
 * File name: Operator.java
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

import java.util.Collections;
import java.util.Set;
import java.util.HashMap;

/**
 * Represents the logical connectives in {@link NarySpiderDiagram}s.
 * <p>This class is the base of all operators in Speedith, and provides methods
 * for querying the available operators (the ones supported in Isabelle) and
 * functionality for creating operators from strings (see methods {@link
 * Operator#fromString(java.lang.String)}).</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Operator {

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The name of the 'CONJUNCTION' operator.
     */
    public static final String OP_NAME_AND = "op &&";
    /**
     * The name of the 'IMPLICATION' operator.
     */
    public static final String OP_NAME_IMP = "op -->";
    /**
     * The name of the 'NEGATION' operator.
     */
    public static final String OP_NAME_NOT = "op not";
    /**
     * The name of the 'DISJUNCTION' operator.
     */
    public static final String OP_NAME_OR = "op ||";
    /**
     * The name of the 'EQUIVALENCE' operator.
     */
    public static final String OP_NAME_EQ = "op <-->";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private int arity;
    private String name;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    private Operator(int arity, String name) {
        this.arity = arity;
        this.name = name;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Static Methods">
    /**
     * Returns the operator with the given name.
     * <p>For a list of all known operators see {@link Operator#knownOperatorNames()}.</p>
     * @param operatorName the name of the operator to fetch.
     * <p>This method returns {@code null} if the operator name is not known or
     * if this parameter is {@code null}.</p>
     * @return a Speedith internal operator.
     */
    public static Operator fromString(String operatorName) {
        return OperatorRegistry.KnownOperators.get(operatorName);
    }

    /**
     * Returns an unmodifiable set of known operator names.
     * <p>Use {@link Operator#fromString(java.lang.String)} to get an operator
     * by name.</p>
     * <p>All the names of known operators are specified in the following
     * fields:
     *  <ul>
     *      <li>{@link Operator#OP_NAME_AND},</li>
     *      <li>{@link Operator#OP_NAME_EQ},</li>
     *      <li>{@link Operator#OP_NAME_IMP},</li>
     *      <li>{@link Operator#OP_NAME_NOT} and</li>
     *      <li>{@link Operator#OP_NAME_OR}.</li>
     *  </ul>
     * </p>
     * @return an unmodifiable set of known operator names.
     */
    public static Set<String> knownOperatorNames() {
        return Collections.unmodifiableSet(OperatorRegistry.KnownOperators.keySet());
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * The number of operands this operator takes.
     * @return the number of operands this operator takes.
     */
    public int getArity() {
        return arity;
    }

    /**
     * The internal name of this operator.
     * @return the internal name of this operator.
     */
    public String getName() {
        return name;
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Operators have unique names (regardless of their arity). Thus one can
     * determine which operator they are dealing with just its name.
     * <p>This function checks whether this operator has the given name and
     * returns {@code true} iff the name of this parameter equals to the one
     * given through the {@code name} argument.</p>
     * <p>Here is a list of known operators:
     *  <ul>
     *      <li>{@link Operator#OP_NAME_AND},</li>
     *      <li>{@link Operator#OP_NAME_EQ},</li>
     *      <li>{@link Operator#OP_NAME_IMP},</li>
     *      <li>{@link Operator#OP_NAME_NOT} and</li>
     *      <li>{@link Operator#OP_NAME_OR}.</li>
     *  </ul>
     * </p>
     * @param name does this operator have this name?
     * @return {@code true} iff the name of this parameter equals to the one
     * given through the {@code name} argument.
     */
    public boolean equals(String name) {
        return getName().equals(name);
    }
    
    /**
     * Returns {@code true} iff this operator equals to the given one (by
     * reference).
     * @param other the operator to compare this one against.
     * @return {@code true} iff this operator equals to the given one (by
     * reference).
     */
    public boolean equals(Operator other) {
        return this == other;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Operator other = (Operator) obj;
        if (this.arity != other.arity) {
            return false;
        }
        if ((this.name == null) ? (other.name != null) : !this.name.equals(other.name)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return name.hashCode() + arity;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Helper Classes">
    /**
     * This class serves as a container of known operators for lazy loading and
     * thread-safety reasons.
     */
    private static class OperatorRegistry {

        /**
         * A map of all operators known by Speedith (where the key equals to the
         * {@link Operator#getName() name} of the operator.
         */
        public static final HashMap<String, Operator> KnownOperators = new HashMap<String, Operator>();

        static {
            KnownOperators.put(OP_NAME_NOT, new Operator(1, OP_NAME_NOT));
            KnownOperators.put(OP_NAME_AND, new Operator(2, OP_NAME_AND));
            KnownOperators.put(OP_NAME_OR, new Operator(2, OP_NAME_OR));
            KnownOperators.put(OP_NAME_IMP, new Operator(2, OP_NAME_IMP));
            KnownOperators.put(OP_NAME_OR, new Operator(2, OP_NAME_EQ));
        }

        private OperatorRegistry() {
        }
    }
    // </editor-fold>
}
