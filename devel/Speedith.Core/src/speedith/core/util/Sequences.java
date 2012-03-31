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

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.*;

/**
 * Contains utility methods for common operations on sequences ({@link
 * Collection collections}, {@link List lists}, and {@link Iterable iterable}
 * sequences in general).
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Sequences {
    
    // <editor-fold defaultstate="collapsed" desc="Printing Methods">
    /**
     * Prints the contents of the given list to the writer output.
     * <p>Note: this method calls the {@link Object#toString()} method on
     * non-null elements, otherwise it prints an empty string.</p>
     * @param list the list whose elements to print to the given writer.
     * @param output the output where to write the elements to (may not be
     * {@code null}).
     * @param openingString the opening string (usually the opening parenthesis)
     * of the printed list.
     * @param closingString the closing string (usually the closing parenthesis)
     * of the printed list.
     * @param delimiter the string to print between separate elements (usually a
     * a comma, followed by a blank space, i.e.: ', ').
     * @throws IOException this exception is thrown if an error occurred while
     * writing to the output.
     */
    public static void print(Iterable<? extends Object> list, Writer output, String openingString, String closingString, String delimiter) throws IOException {
        if (output == null) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "output"));
        }
        output.append(openingString);
        if (list != null) {
            Iterator<? extends Object> itr = list.iterator();
            if (itr.hasNext()) {
                Object el = itr.next();
                output.append(el == null ? "" : el.toString());
                while (itr.hasNext()) {
                    el = itr.next();
                    output.append(delimiter);
                    if (el != null) {
                        output.append(el.toString());
                    }
                }
            }
        }
        output.append(closingString);
    }

    /**
     * This method is a shorthand for <span style="font-style:italic;font-family:monospace;">
     * {@link Sets#print(java.lang.Iterable, java.io.Writer, java.lang.String,
     * java.lang.String, java.lang.String) print}(list,
     * stringWriter, "[", "]", ", ")</span>.
     * @param list the list whose elements to print to the given writer.
     * @return the printed string version of the sequence.
     */
    public static String toString(Iterable<? extends Object> list) {
        StringWriter sw = new StringWriter();
        try {
            Sequences.print(list, sw, "[", "]", ", ");
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
        return sw.toString();
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Mapping methods">
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
