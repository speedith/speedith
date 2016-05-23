/*
 *   Project: Speedith.Core
 * 
 * File name: MultipleRuleArgs.java
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
package speedith.core.reasoning.args;

import speedith.core.reasoning.RuleApplicationException;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import static java.util.Arrays.asList;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class MultipleRuleArgs implements RuleArg, Iterable<RuleArg>, Serializable {

    private static final long serialVersionUID = -2168028613782815627L;
    private final ArrayList<RuleArg> ruleArgs;

    public MultipleRuleArgs(List<? extends RuleArg> ruleArgs) {
        this.ruleArgs = new ArrayList<>(ruleArgs);
    }

    public MultipleRuleArgs(RuleArg... ruleArgs) {
        this(asList(ruleArgs));
    }

    public RuleArg get(int index) {
        return ruleArgs.get(index);
    }

    public Iterator<RuleArg> iterator() {
        return ruleArgs.iterator();
    }

    public int size() {
        return ruleArgs.size();
    }

    public boolean isEmpty() {
        return ruleArgs.isEmpty();
    }

    public List<RuleArg> getRuleArgs() {
        return Collections.unmodifiableList(ruleArgs);
    }

    public static void assertArgumentsNotEmpty(MultipleRuleArgs multipleRuleArgs) throws RuleApplicationException {
        if (multipleRuleArgs.isEmpty()) {
            throw new RuleApplicationException("No inference rule arguments were specified.");
        }
    }
}
