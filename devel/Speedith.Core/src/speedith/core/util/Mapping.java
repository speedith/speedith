/*
 *   Project: Speedith.Core
 * 
 * File name: Mapping.java
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
package speedith.core.util;

/**
 * This interface corresponds to a function, which maps an instance of type {@code 
 * TIn} to an instance of the type {@code TOut}.
 * @param <TIn> The type of the input object, which is to be mapped to an object
 * of type {@code TOut}.
 * @param <TOut> The type of the object to which the input parameter maps.
 * @param <TEx> The type of exception this mapping throws if the mapping of a
 * particular element fails.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface Mapping<TIn, TOut, TEx extends Throwable> {
    /**
     * This function maps the input parameter of type {@code TIn} to an instance
     * of the type {@code TOut}.
     * @param inst the input parameter to map.
     * @return the mapped object.
     * @throws TEx  the exception thrown if the mapping of a particular element
     * fails.
     */
    TOut apply(TIn inst) throws TEx;
}
