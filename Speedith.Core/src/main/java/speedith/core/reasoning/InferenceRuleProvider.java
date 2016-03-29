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

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.args.RuleArg;

import java.util.Locale;
import java.util.Set;

/**
 * Contains detailed information about the inference rules it provides (through
 * the {@link InferenceRules factory of inference rules}). <p>Instances of
 * classes that implement interface provide the following information: <ul>
 * <li>an explanation of what the {@link InferenceRule inference rule} does (for
 * the user),</li> <li>a description of parameters it takes (for the user as
 * well as for the SRK), and</li> <li>instructions on how to obtain the
 * parameters (for the user and the UI).</li> </ul> </p>
 *
 * @param <TArgs> the type of arguments the provided inference rule expects. Use
 * the type {@link RuleArg} to specify that the inference rule does not expect
 * any specific arguments.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface InferenceRuleProvider<TArgs extends RuleArg> extends InferenceProvider<TArgs> {

    /**
     * Returns an instance of the {@link InferenceRule inference rule} this
     * class provides. <p>Note that the main purpose of this class is to give
     * more information on the inference rule, without having to create an
     * actual instance of the inference rule itself. For example, this class
     * provides information on what arguments the inference rule accepts, a
     * description on how it can be used, and what its effects are.</p> <p><span
     * style="font-weight:bold">Note</span>: this method may return the same
     * instance of the inference rule for many invocations.</p>
     *
     * @return the actual inference rule.
     */
    InferenceRule<TArgs> getInferenceRule();

    /**
     * Returns the type of the inference rule instances which are returned by
     * {@link InferenceRuleProvider#getInferenceRule()}.
     *
     * @return the type of the inference rule instances which are returned by
     * {@link InferenceRuleProvider#getInferenceRule()}.
     */
    Class<? extends InferenceRule<TArgs>> getInferenceRuleType();

    /**
     * Indicates whether the inference rule returned by
     * {@link InferenceRuleProvider#getInferenceRule()} is a <span
     * style="font-style:italic;">forward-style</span> rule.
     *
     * <p>Forward-style rules are the ones which take a spider diagram <span
     * style="font-style:italic;">A</span> and produce an entailed spider
     * diagram <span style="font-style:italic;">A'</span>.
     *
     * <div><span style="font-style:italic;">A</span> &#x27F9; <span
     * style="font-style:italic;">A'</span></div>
     *
     * </p>
     *
     * <p>An {@link InferenceRule inference rule} is forward-style if it
     * implements the {@link ForwardRule} interface.</p>
     *
     * @return a value that indicates whether the inference rule returned by
     * {@link InferenceRuleProvider#getInferenceRule()} is a <span
     * style="font-style:italic;">forward-style</span> rule.
     */
    boolean isForwardRule();




    /**
     * Returns a pretty human-readable short name of the category of the
     * provided inference rule.
     *
     * @return a pretty human-readable short name of the category of the
     * provided inference rule.
     */
    String getCategory();

    /**
     * Returns a pretty human-readable short name of the category of the
     * provided inference rule.
     *
     * @param locale the locale to which to translate the returned string.
     * @return a pretty human-readable short name of the category of the
     * provided inference rule.
     */
    String getCategory(Locale locale);


    /**
     * Returns instructions on how to apply the provided inference rule. <p>This
     * includes: <ul><li>instructions for the user on how to obtain the
     * parameters for a successful rule application, and</li><li>programmatic
     * instructions for the UI (on how to display the selection steps and how to
     * produce the final parameter for the rule).</li></ul>.</p>
     *
     * @return the rule application instructions for the provided inference
     * rule.
     */
    RuleApplicationInstruction<TArgs> getInstructions();

    /**
     * Returns the {@link InferenceRuleProvider#getPrettyName() pretty name} of
     * the inference rule this provided provides.
     *
     * @return the {@link InferenceRuleProvider#getPrettyName() pretty name} of
     * the inference rule this provided provides.
     */
    @Override
    String toString();


}
