/*
 *   Project: Speedith.Core
 * 
 * File name: Sequences.java
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * Contains utility methods for common operations on sequences ({@link
 * Collection collections}, {@link List lists}, and {@link Iterable iterable}
 * sequences in general).
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Sequences {
    // <editor-fold defaultstate="collapsed" desc="Iterable helper methods">

    /**
     * Maps every element in {@code seq} to an element of type {@code TOut} and
     * puts them into a {@link LinkedList linked list}.
     *
     * @param <TIn> The type of the input objects, which are to be mapped to
     * objects of type {@code TOut}.
     * @param <TOut> The type of the objects to which the input parameters map.
     * @param seq the sequence of elements to map. If this parameter is {@code
     * null}, so will be the result.
     * @param <TEx> The type of exception this mapping throws if the mapping of
     * a particular element fails.
     * @param mapper the function that maps each element in {@code seq} to an
     * object of type {@code TOut}.
     * @return a {@link LinkedList linked list} of objects mapped from {@code
     * seq}. Note that the resulting linked list will have the same number of
     * elements as {@code seq}. Also, if {@code seq} is {@code null}, so will be
     * the result.
     * @throws TEx the exception thrown if the mapping of a particular element
     * fails.
     * @throws IllegalArgumentException this exception is thrown if the {@code mapper}
     * is {@code null}.
     */
    public static <TIn, TOut, TEx extends Throwable> LinkedList<? super TOut> map(Iterable<TIn> seq, Mapping<TIn, ? extends TOut, TEx> mapper) throws TEx {
        if (mapper == null) {
            throw new IllegalArgumentException("The argument 'mapper' must not be null.");
        }
        if (seq == null) {
            return null;
        } else {
            LinkedList<TOut> result = new LinkedList<TOut>();
            for (TIn el : seq) {
                result.add(mapper.apply(el));
            }
            return result;
        }
    }

    /**
     * Maps every element in {@code seq} to an element of type {@code TOut} and
     * puts them into a {@link ArrayList array list}.
     *
     * @param <TIn> The type of the input objects, which are to be mapped to
     * objects of type {@code TOut}.
     * @param <TOut> The type of the objects to which the input parameters map.
     * @param <TEx> The type of exception this mapping throws if the mapping of
     * a particular element fails.
     * @param seq the sequence of elements to map. If this parameter is {@code
     * null}, so will be the result.
     * @param mapper the function that maps each element in {@code seq} to an
     * object of type {@code TOut}.
     * @return a {@link ArrayList array list} of objects mapped from {@code
     * seq}. Note that the resulting list will have the same number of elements
     * as {@code seq}. Also, if {@code seq} is {@code null}, so will be the
     * result.
     * @throws TEx the exception thrown if the mapping of a particular element
     * fails.
     * @throws IllegalArgumentException this exception is thrown if the {@code mapper}
     * is {@code null}.
     */
    public static <TIn, TOut, TEx extends Throwable> ArrayList<TOut> map(List<TIn> seq, Mapping<TIn, ? extends TOut, TEx> mapper) throws TEx {
        if (mapper == null) {
            throw new IllegalArgumentException("The argument 'mapper' must not be null.");
        }
        if (seq == null) {
            return null;
        } else {
            ArrayList<TOut> result = new ArrayList<TOut>(seq.size());
            for (TIn el : seq) {
                result.add(mapper.apply(el));
            }
            return result;
        }
    }
    // </editor-fold>
}
