/*
 *   Project: Speedith.Core
 * 
 * File name: SortedSets.java
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
package speedith.core.util;

import java.util.Comparator;
import java.util.Iterator;
import java.util.SortedSet;
import static speedith.core.i18n.Translations.i18n;

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
     * pair in the order they appear in the set via the sets' iterators). It
     * returns:
     * <p>
     * <ul>
     *   <li> {@code -1} if either of the two is true:
     *      <ul>
     *          <li>the first set contains the first such element that is
     *          smaller when compared to the element of the second set (at the
     *          same position).</li>
     *          <li>if the first set is contained entirely in the second set and
     *          the second set contains only larger elements.</li>
     *      </ul>
     *   <li> {@code 0} when the two sets are equal, if both are null or empty,
     *        or if one of them is null and the other is empty.</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     * </p>
     * <p>Note: if one of the sets is {@code null}, it will be treated as
     * an empty set (a {@code null} set thus equals to the empty set, and it is
     * in effect smaller than any non-empty set).</p>
     * <p>Important: this method uses the comparators of the given sets. If the
     * comparators of the two given sets are not the same, or if none of the
     * sets provide any comparators, an {@link IllegalArgumentException}
     * exception will be thrown.</p>
     * @param <E> the type of the elements in the set.
     * @param s1 the first set.
     * @param s2 the second set.
     * @return one of the following:
     * <ul>
     *   <li> {@code -1} if either of the two is true:
     *      <ul>
     *          <li>the first set contains the first such element that is
     *          smaller when compared to the element of the second set (at the
     *          same position).</li>
     *          <li>if the first set is contained entirely in the second set and
     *          the second set contains only larger elements.</li>
     *      </ul>
     *   <li> {@code 0} when the two sets are equal, if both are null or empty,
     *        or if one of them is null and the other is empty.</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     */
    public static <E> int compare(SortedSet<E> s1, SortedSet<E> s2) {
        if (s1 == s2) {
            // The sets are the same.
            return 0;
        } else if (s1 == null || s1.isEmpty()) {
            // If the first set is empty, then just check whether the second one
            // is too, otherwise the second one will be invariably greater then.
            return (s2 == null || s2.isEmpty()) ? 0 : -1;
        } else if (s2 == null || s2.isEmpty()) {
            // If the second set is empty then it should compare lower to the
            // first set (which we know is not empty)
            return 1;
        } else {
            // Neither of the sets is either null or empty. Compare them.
            Comparator<? super E> comparator = s1.comparator();
            if (s2.comparator() != comparator) {
                // Both of the sets provide comparators, but the two comparators
                // are not the same. This is an illegal situation.
                throw new IllegalArgumentException(i18n("ERR_SORTED_SETS_COMPARATORS_DIFFER"));
            } else if (comparator == null) {
                throw new IllegalArgumentException(i18n("ERR_SORTED_SETS_NO_COMPARATOR"));
            }
            // Use natural ordering
            Iterator<E> i1 = s1.iterator(),
                    i2 = s2.iterator();
            // Start the comparison
            while (i1.hasNext() && i2.hasNext()) {
                E el1 = i1.next();
                E el2 = i2.next();
                int retVal = comparator.compare(el1, el2);
                if (retVal != 0)
                    return Integer.signum(retVal);
            }
            // Okay, if we reached this point, then the two sets share the same
            // head and at least one of them has ended.
            return i1.hasNext() ? 1 : (i2.hasNext() ? -1 : 0);
        }
    }

    /**
     * Compares the elements in the two sorted sets lexicographically (pair by
     * pair in the order they appear in the set via the sets' iterators). It
     * returns:
     * <p>
     * <ul>
     *   <li> {@code -1} if either of the two is true:
     *      <ul>
     *          <li>the first set contains the first such element that is
     *          smaller when compared to the element of the second set (at the
     *          same position).</li>
     *          <li>if the first set is contained entirely in the second set and
     *          the second set contains only larger elements.</li>
     *      </ul>
     *   <li> {@code 0} when the two sets are equal, if both are null or empty,
     *        or if one of them is null and the other is empty.</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     * </p>
     * <p>Note: if one of the sets is {@code null}, it will be treated as
     * an empty set (a {@code null} set thus equals to the empty set, and it is
     * in effect smaller than any non-empty set).</p>
     * <p>Important: this method uses the {@link Comparable} interface, which
     * should be implemented by the elements of the two given sets.</p>
     * @param <E> the type of the elements in the set.
     * @param s1 the first set.
     * @param s2 the second set.
     * @return one of the following:
     * <ul>
     *   <li> {@code -1} if either of the two is true:
     *      <ul>
     *          <li>the first set contains the first such element that is
     *          smaller when compared to the element of the second set (at the
     *          same position).</li>
     *          <li>if the first set is contained entirely in the second set and
     *          the second set contains only larger elements.</li>
     *      </ul>
     *   <li> {@code 0} when the two sets are equal, if both are null or empty,
     *        or if one of them is null and the other is empty.</li>
     *   <li> {@code 1} otherwise.</li>
     * </ul>
     */
    public static <E extends Comparable<E>> int compareNaturally(SortedSet<E> s1, SortedSet<E> s2) {
        if (s1 == s2) {
            // The sets are the same.
            return 0;
        } else if (s1 == null || s1.isEmpty()) {
            // If the first set is empty, then just check whether the second one
            // is too, otherwise the second one will be invariably greater then.
            return (s2 == null || s2.isEmpty()) ? 0 : -1;
        } else if (s2 == null || s2.isEmpty()) {
            // If the second set is empty then it should compare lower to the
            // first set (which we know is not empty)
            return 1;
        } else {
            // Use natural ordering
            Iterator<E> i1 = s1.iterator(),
                    i2 = s2.iterator();
            // Start the comparison
            while (i1.hasNext() && i2.hasNext()) {
                E el1 = i1.next();
                E el2 = i2.next();
                // Compare the current two elements. If exactly one of them is
                // null, then use the other to compare them. If both are null,
                // consider them the same.
                if (el1 == null) {
                    if (el2 != null) {
                        int retVal = el2.compareTo(el1);
                        if (retVal != 0)
                            return Integer.signum(-retVal);
                    }
                } else if (el2 != null) {
                    int retVal = el1.compareTo(el2);
                    if (retVal != 0)
                        return Integer.signum(retVal);
                }
            }
            // Okay, if we reached this point, then the two sets share the same
            // head and at least one of them has ended.
            return i1.hasNext() ? 1 : (i2.hasNext() ? -1 : 0);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private SortedSets() {
    }
    // </editor-fold>
}
