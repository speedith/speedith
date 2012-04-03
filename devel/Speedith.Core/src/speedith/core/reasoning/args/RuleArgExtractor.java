/*
 *   Project: Speedith.Core
 * 
 * File name: RuleArgExtractor.java
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

import java.util.Map;
import speedith.core.reasoning.args.RuleArg;

/**
 * Implementations of this interface provide conversions from a map of objects
 * to rule arguments.
 *
 * @param <T> the type of produced rule arguments.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface RuleArgExtractor<T extends RuleArg> {

    // <editor-fold defaultstate="collapsed" desc="Common Object Names">
    /**
     * The name of an object that tells the subgoal index (on which to apply the
     * inference rule).
     */
    static final String SubgoalIndex = "subgoal index";
    /**
     * The name of an object that tells the subdiagram index (on which to apply
     * the inference rule).
     */
    static final String SubdiagramIndex = "subdiagram index";
    /**
     * The name of an object that tells the name of the spider (on which to
     * apply the inference rule).
     */
    static final String SpiderName = "spider name";
    /**
     * The name of an object that tells the zone (on which to
     * apply the inference rule).
     */
    static final String Zone = "zone";
    /**
     * The name of an object that tells the region (on which to
     * apply the inference rule).
     */
    static final String Region = "region";
    /**
     * The name of an object that tells the name of the contour (on which to
     * apply the inference rule).
     */
    static final String ContourLabel = "contour label";
    // </editor-fold>

    /**
     * Returns a map of object names and types that this rule argument extractor
     * expects (or understands).
     *
     * @return a map of object names and types that this rule argument extractor
     * expects (or understands).
     */
    Map<String, Class<?>> getSupportedObjectNames();

    /**
     * Given a map of object names and their corresponding objects, this method
     * returns a {@link RuleArg rule argument} that can be used in an inference
     * rule.
     *
     * @param objects the map of objects from which to construct the inference
     * rule arguments.
     * @return the arguments that can be used in an inference rule.
     * @throws RuleArgExtractionException thrown if the extraction of the
     * inference rule arguments failed (for any reason).
     */
    T extractRuleArg(Map<String, Object> objects) throws RuleArgExtractionException;
}
