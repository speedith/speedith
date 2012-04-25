/*
 *   Project: Speedith.Core
 * 
 * File name: ForwardRule.java
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

/**
 * {@link InferenceRule Inference rules} implementing this interface may be
 * applied in forward-style proofs.
 *
 * <p>Forward-style rules are the ones which take a spider diagram <span
 * style="font-style:italic;">A</span> and produce an entailed spider diagram
 * <span style="font-style:italic;">A'</span>.
 *
 * <div><span style="font-style:italic;">A</span> &#x27F9; <span
 * style="font-style:italic;">A'</span></div>
 *
 * </p>
 *
 * @param <TArgs> the type of arguments the provided inference rule expects. Use
 * the type {@link RuleArg} to specify that the inference rule does not expect
 * any specific arguments.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface ForwardRule<TArgs extends RuleArg> extends InferenceRule<TArgs> {

    /**
     * Makes an inference step on the given goals in a backwards manner.
     *
     * <p>A forwards rule changes goals <span style="font-family:serif">[
     * &#x229A;<sub>[1 &#x2264; <span style="font-style:italic;">i</span>
     * &#x2264; n]</sub> <span style="font-style:italic;">G<sub>i</sub></span>
     * ]</span> so that the resulting rules <span style="font-family:serif">[
     * &#x229A;<sub>[1 &#x2264; <span style="font-style:italic;">i</span>
     * &#x2264; n]</sub> <span style="font-style:italic;">G'<sub>i</sub></span>
     * ]</span>, where &#x229A; &#x2208; {&#x22C0;, &#x22C1;}, are implied
     * (logically entailed) by the original ones:
     *
     * <div style="padding-left: 2em; font-family:serif;"><span
     * style="font-family:serif">[ &#x229A;<sub>[1 &#x2264; <span
     * style="font-style:italic;">i</span> &#x2264; n]</sub> <span
     * style="font-style:italic;">G<sub>i</sub></span> ]</span> &#x27F9; <span
     * style="font-family:serif">[ &#x229A;<sub>[1 &#x2264; <span
     * style="font-style:italic;">i</span> &#x2264; n]</sub> <span
     * style="font-style:italic;">G'<sub>i</sub></span> ]</span>,</div>
     *
     * where &#x229A; &#x2208; {&#x22C0;, &#x22C1;}. </p>
     *
     * @param args the arguments to the inference rule. For more information see
     * {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * }.
     * @param goals the goals on which the inference rule should act. For more
     * information see
     * {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * }.
     * @return the changed goals. For more information see
     * {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * }.
     * @throws RuleApplicationException thrown if the inference rule could not
     * be applied on the given goals with the given arguments.
     */
    RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException;
}
