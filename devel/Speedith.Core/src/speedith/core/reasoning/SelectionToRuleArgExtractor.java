/*
 *   Project: Speedith.Core
 * 
 * File name: SelectionToRuleArgExtractor.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
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

import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.selection.SelectionSequence;

/**
 * Converts the user's selection of diagrammatic elements to a rule argument.
 * This is used, for example, in providing sufficient arguments to an inference
 * rule.
 *
 * @param <T> the type of rule arguments this extractor returns.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface SelectionToRuleArgExtractor<T extends RuleArg> {

    /**
     * Gets the {@link RuleArg arguments} from the successful user's selection.
     * The returned arguments can be passed to the {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals) apply method}
     * of the inference rule.
     *
     * @param selectionSequence the user's selection from which to extract the
     * rule argument.
     * @param subgoalIndex the index of the subgoal on which the inference rule
     * should be applied.
     * @return the extracted arguments.
     */
    T extractRuleArg(SelectionSequence selectionSequence, int subgoalIndex);
}
