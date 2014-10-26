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
import java.util.HashMap;
import java.util.Set;

/**
 * Represents the logical connectives in {@link CompoundSpiderDiagram}s.
 * <p>This class is the base of all operators in Speedith, and provides methods
 * for querying the available operators (the ones supported in Isabelle) and
 * functionality for creating operators from strings (see methods {@link
 * Operator#fromString(java.lang.String)}).</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public enum Operator {

  /**
   * The 'negation' operator.
   */
  Negation("op not", 1),
  /**
   * The 'conjunction' operator.
   */
  Conjunction("op &", 2),
  /**
   * The 'disjunction' operator.
   */
  Disjunction("op |", 2),
  /**
   * The 'implication' operator.
   */
  Implication("op -->", 2),
  /**
   * The 'equivalence' operator.
   */
  Equivalence("op <-->", 2);

  private final String name;
  private final int arity;

  private Operator(String name, int arity) {
    this.name = name;
    this.arity = arity;
  }

  /**
   * Returns the name of the operator.
   *
   * @return the name of the operator.
   */
  public String getName() {
    return name;
  }

  /**
   * Returns the 'negation' operator.
   *
   * @return the 'negation' operator.
   */
  public static Operator getNegation() {
    return Negation;
  }

  /**
   * Returns the 'implication' operator.
   *
   * @return the 'implication' operator.
   */
  public static Operator getImplication() {
    return Implication;
  }

  /**
   * Returns the 'equivalence' operator.
   *
   * @return the 'equivalence' operator.
   */
  public static Operator getEquivalence() {
    return Equivalence;
  }

  /**
   * Returns the 'disjunction' operator.
   *
   * @return the 'disjunction' operator.
   */
  public static Operator getDisjunction() {
    return Disjunction;
  }

  /**
   * Returns the 'conjunction' operator.
   *
   * @return the 'conjunction' operator.
   */
  public static Operator getConjunction() {
    return Conjunction;
  }

  /**
   * The number of operands this operator takes.
   *
   * @return the number of operands this operator takes.
   */
  public int getArity() {
    return arity;
  }

  /**
   * Returns the name of the operator.
   *
   * @return the name of the operator.
   */
  @Override
  public String toString() {
    return this.getName();
  }

  /**
   * Operators have unique names (regardless of their arity). Thus one can
   * determine which operator they are dealing with just its name.
   * <p>This function checks whether this operator has the given name and
   * returns {@code true} iff the name of this parameter equals to the one
   * given through the {@code name} argument.</p>
   * <p>Here is a list of known operators:
   * <ul>
   * <li>{@link Operator#Conjunction},</li>
   * <li>{@link Operator#Equivalence},</li>
   * <li>{@link Operator#Implication},</li>
   * <li>{@link Operator#Negation} and</li>
   * <li>{@link Operator#Disjunction}.</li>
   * </ul>
   * </p>
   *
   * @param name does this operator have this name?
   * @return {@code true} iff the name of this parameter equals to the one
   * given through the {@code name} argument.
   */
  public boolean equals(String name) {
    return getName().equals(name);
  }

  /**
   * Returns the operator with the given name.
   * <p>For a list of all known operators see {@link Operator#knownOperatorNames()}.</p>
   *
   * @param operatorName the name of the operator to fetch.
   *                     <p>This method returns {@code null} if the operator name is not known or
   *                     if this parameter is {@code null}.</p>
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
   * <ul>
   * <li>{@link Operator#Conjunction},</li>
   * <li>{@link Operator#Disjunction},</li>
   * <li>{@link Operator#Equivalence},</li>
   * <li>{@link Operator#Implication} and</li>
   * <li>{@link Operator#Negation}.</li>
   * </ul>
   * </p>
   *
   * @return an unmodifiable set of known operator names.
   */
  public static Set<String> knownOperatorNames() {
    return Collections.unmodifiableSet(OperatorRegistry.KnownOperators.keySet());
  }

  /**
   * This class serves as a container of known operators for lazy loading and
   * thread-safety reasons.
   */
  private static class OperatorRegistry {

    /**
     * A map of all operators known by Speedith (where the key equals to the
     * {@link Operator#getName() name} of the operator.
     */
    public static final HashMap<String, Operator> KnownOperators = new HashMap<>();

    static {
      for (Operator operator : Operator.values()) {
        KnownOperators.put(operator.getName(), operator);
      }
    }

    private OperatorRegistry() {
    }
  }
}
