/*
 *   Project: Speedith.Core
 * 
 * File name: package-info.java
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

/**
 * This package contains the Speedith Reasoning Kernel (or
 * <span style="font-style:italic;">SRK</span>).
 * <p>SRK is an API that provides a subsystem for reasoning with {@link
 * speedith.core.lang.SpiderDiagram spider diagrams}.</p>
 * <p>SRK provides the following features:
 *  <ul>
 *      <li>
 *          <span style="font-weight:bold">Inference rule application</span>:
 *          manages the application of inference rules on spider diagrams. It
 *          provides the ability for a sequential composition of inference
 *          rules (i.e.: applying a new inference rule on a particular spider
 *          diagram, removing the last applied inference rule etc.).
 *      </li>
 *      <li>
 *          <span style="font-weight:bold">Proof trace</span>:
 *          keeps a browsable and exportable history of currently applied
 *          inference rules.
 *      </li>
 *      <li>
 *          <span style="font-weight:bold">Proof state</span>:
 *          manages a proof state (i.e.: the initial spider-diagrammatic goal
 *          with subsequent intermediate subgoals). Inference rules act on the
 *          current proof state (which contains a set of spider diagrams as a
 *          set of remaining proof obligations). The inference rule can pick any
 *          one or more spider diagrams from the current proof state.
 *          TODO: Think about how the user can specify on which subgoal to apply
 *          the inference rule (maybe have inference rules that work on many
 *          subgoals -- provide many interfaces to the inference rules? one for
 *          single subgoal- and the other for multiple subgoal- inference
 *          rules).
 *      </li>
 *  </ul>
 * </p>
 */
package speedith.core.reasoning;
