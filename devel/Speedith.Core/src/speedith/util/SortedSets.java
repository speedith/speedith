/*
 *   Project: Speedith.Core
 * 
 * File name: SortedSets.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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
package speedith.util;

import java.util.Comparator;
import java.util.SortedSet;

/**
 * Provides some utility functions for sorted sets (e.g.:
 * {@link SortedSets#compare(java.util.SortedSet, java.util.SortedSet)
 * comparison}).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class SortedSets {

    // <editor-fold defaultstate="collapsed" desc="Public Static Methods">
    /**
     * Compares the elements in the two sorted sets lexicographically (pair by
     * pair) and returns:
     * <ul>
     *   <li> {@code -1} when the smaller element in the first non-equal pair is
     *        from the first set, or when the first set is the head of the
     *        second set (i.e.: its subset).</li>
     *   <li> {@code 0} when the two sets are equal, if both are null or empty,
     *        or if one of them is null and the other is empty).</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     * <p>Note: if one of the sets is {@code null}, it will be considered as
     * an empty set (an empty set equals to a {@code null} set, and it is also
     * smaller than any non-empty set).</p>
     * <p>Important: the comparator used will be the one given by the sorted
     * sets (provided both are the same). If these comparators are not the same,
     * an {@link IllegalArgumentException} exception will be thrown. If the
     * sets do not provide comparators, this
     * method will try to cast the separate elements to {@link Comparable} and
     * compare them via the {@link Comparable#compareTo(java.lang.Object)
     * compareTo} method.</p>
     * @param <E> the type of the elements in the set.
     * @param s1 the first set.
     * @param s2 the second set.
     * @return one of the following:
     * <ul>
     *   <li> {@code -1} when the smaller element in the first non-equal pair is
     *        from the first set, or when the first set is the head of the
     *        second set (i.e.: its subset).</li>
     *   <li> {@code 0} when the two sets are equal.</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     */
    public static <E> int compare(SortedSet<E> s1, SortedSet<E> s2) {
        if (s1 == null) {
            return (s2 == null || s2.isEmpty()) ? 0 : -1;
        } else if (s2 == null) {
            return s1.isEmpty() ? 0 : 1;
        } else if (s1 == s2) {
            return 0;
        } else {
            Comparator<? super E> comparator = s1.comparator();
            if (s2.comparator() != comparator)
                throw new IllegalArgumentException();
            if (comparator == null) {
                // TODO: Use natural ordering
            } else {
                // TODO: Use the comparator
            }
            return 0;
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Hidden Constructor">
    private SortedSets() {
    }
    // </editor-fold>
}
