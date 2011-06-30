/*
 *   Project: Speedith.Core
 * 
 * File name: InferenceRuleProvider.java
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
package speedith.core.reasoning;

/**
 * Contains detailed information about the inference rules it provides (through
 * the {@link InferenceRules factory of inference rules}).
 * <p>Instances of classes that implement interface provide the following
 * information:
 *  <ul>
 *      <li>an explanation of what the {@link InferenceRule inference rule} does
 *          (for the user),</li>
 *      <li>a description of parameters it takes (for the user as well as for
 *          the SRK),</li>
 *      <li>TODO (others?).</li>
 *  </ul>
 * </p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface InferenceRuleProvider {
    /**
     * Returns an instance of the {@link InferenceRule inference rule} this
     * class provides.
     * <p>Note that the main purpose of this class is to give more
     * information on the inference rule, without having to create an actual
     * instance of the inference rule itself. For example, this class provides
     * information on what arguments the inference rule accepts, a description
     * on how it can be used, and what its effects are.</p>
     * <p><span style="font-weight:bold">Note</span>: this method may return the
     * same instance of the inference rule for many invocations.</p>
     * @return 
     */
    public InferenceRule getInferenceRule();

    /**
     * Returns the name of the {@link InferenceRule} this provider provides.
     * <p><span style="font-weight:bold">Note</span>: this name is not
     * internationalised.</p>
     * @return the name of the {@link InferenceRule} this provider provides.
     */
    public String getInferenceRuleName();
}
