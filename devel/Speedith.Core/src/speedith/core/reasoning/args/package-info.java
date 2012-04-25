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
 * A collection of arguments that can be passed to inference rules. Each
 * inference rule, when applied to some {@link speedith.core.reasoning.Goals
 * goals}, may take some arguments, which tell the inference rule how exactly to
 * operate on the goals. For example, the {@link speedith.core.reasoning.rules.SplitSpiders
 * split spiders} inference rule takes an argument of type {@link
 * speedith.core.reasoning.args.SpiderRegionArg}, which tells the rule to split
 * a spider in a specific zone of
 * a specific primary spider diagram in a specific subgoal.
 */
package speedith.core.reasoning.args;
