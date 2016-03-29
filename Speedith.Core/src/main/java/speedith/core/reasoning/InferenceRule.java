/*
 *   Project: Speedith.Core
 * 
 * File name: InferenceRule.java
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

import speedith.core.reasoning.args.*;
import speedith.core.reasoning.rules.SplitSpiders;

/**
 * Specifies the interface of every inference rule. <p>An inference rule can be
 * applied on a set of spider diagrams (the goals) with some parameters (see the
 * {@link RuleArg} interface) and returns a new set of goals (contained in an
 * instance of the {@link RuleApplicationResult} class).</p> <p>Inference rules
 * for spider diagrams are introduced in the paper <a
 * href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924"
 * title="10.1112/S1461157000000942"> Spider Diagrams (2005)</a>.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 *
 * @param <TArgs> the type of arguments the provided inference rule expects. Use
 * the type {@link RuleArg} to specify that the inference rule does not expect
 * any specific arguments.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface InferenceRule<TArgs extends RuleArg>  extends Inference<TArgs, RuleApplicationResult> {

    /**
     * An inference rule in spider diagrams takes a set of goals and returns new
     * goals where the latter logically entail the former.
     *
     * <p>For more information on inference rules for spider diagrams see paper
     * <a
     * href="http://journals.cambridge.org/action/displayAbstract?fromPage=online&aid=6564924"
     * title="10.1112/S1461157000000942"> Spider Diagrams (2005)</a>.</p>
     *
     * @param args the arguments to this inference rule.
     *
     * <p>An example of an argument is in the {@link SplitSpiders split spiders
     * rule}, which operates on a specific spider, in a specific primary
     * diagrams, within a specific zone. Therefore, the arguments to the split
     * spiders rule is of type {@link SpiderRegionArg}, which contains the
     * following parameters:
     *
     * <ul>
     *
     * <li>the {@link SubgoalIndexArg subgoal index},</li>
     *
     * <li>the {@link SubDiagramIndexArg primary diagram index},</li>
     *
     * <li>the {@link SpiderArg spider}, and also the {@link SpiderRegionArg
     *          zone} of one of the feet of the spider where to split it.</li>
     *
     * </ul>
     *
     * </p>
     *
     * @param goals the goals on which to apply the inference rule.
     *
     * <p><span style="font-weight:bold">Note</span>: this object is immutable
     * and is thus suitable for use in the returned {@link
     * RuleApplicationResult} instance.</p>
     *
     * <p><span style="font-weight:bold">Note</span>: this parameter might be
     * {@code null}, which indicates an empty goal set (no proof obligations).
     * The rule may throw an exception to show that it cannot be invoked on an
     * empty proof state.</p>
     *
     * @return results of the application of the inference rule (e.g.: new
     * subgoals).
     *
     * <p><span style="font-weight:bold">Note</span>: can be {@code null} to
     * indicate that the rule managed to discharge all the goals (i.e.: prove
     * them to be true in the current context).</p>
     *
     *
     * @throws RuleApplicationException thrown if the inference rule could not
     * be applied on the given goals with the given arguments.
     */
    @Override
    RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException;

    /**
     * Returns the provider of this rule. This provider gives all the
     * meta-information about this rule (human-readable description, formal
     * properties of the rule like equivalence preserving etc.). <p><span
     * style="font-weight:bold">Note:</span> the return value of this
     * function</p> must not be {@code null}.
     *
     * @return the provider of this rule.
     */
    InferenceRuleProvider<TArgs> getProvider();
}
