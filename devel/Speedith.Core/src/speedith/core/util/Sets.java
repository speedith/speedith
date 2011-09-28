/*
 *   Project: Speedith.Core
 *
 * File name: Sets.java
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

import java.util.Collection;
import java.io.IOException;
import java.io.Writer;
import java.util.Comparator;
import java.util.Iterator;
import java.util.SortedSet;
import static speedith.core.i18n.Translations.i18n;

/**
 * Provides some utility functions for sorted sets (e.g.:
 * {@link Sets#compare(java.util.SortedSet, java.util.SortedSet)
 * comparison}).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Sets {

    // <editor-fold defaultstate="collapsed" desc="Comparison">
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
     * <p><span style="font-weight:bold">Important</span>: this method uses the comparators of the given sets. If the
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
    public static <E> int compare(SortedSet<E> s1, SortedSet<? extends E> s2) {
        int retVal = nullOrEmptyCompare(s1, s2);
        if (retVal == 2) {
            // Neither of the sets is either null or empty. Compare them.
            Comparator<? super E> comparator = getElementComparator(s1, s2);
            Iterator<E> i1 = s1.iterator();
            Iterator<? extends E> i2 = s2.iterator();
            // Start the comparison
            while (i1.hasNext() && i2.hasNext()) {
                retVal = comparator.compare(i1.next(), i2.next());
                if (retVal != 0) {
                    return Integer.signum(retVal);
                }
            }
            // Okay, if we reached this point, then the two sets share the same
            // head and at least one of them has ended.
            return i1.hasNext() ? 1 : (i2.hasNext() ? -1 : 0);
        } else {
            return retVal;
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
     * <p><span style="font-weight:bold">Important</span>: this method uses the {@link Comparable} interface, which
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
    public static <E extends Comparable<? super E>> int compareNaturally(SortedSet<E> s1, SortedSet<? extends E> s2) {
        int retVal = nullOrEmptyCompare(s1, s2);
        if (retVal == 2) {
            // Use natural ordering
            Iterator<E> i1 = s1.iterator();
            Iterator<? extends E> i2 = s2.iterator();
            // Start the comparison
            while (i1.hasNext() && i2.hasNext()) {
                retVal = compare(i1.next(), i2.next());
                if (retVal != 0) {
                    return retVal;
                }
            }
            // Okay, if we reached this point, then the two sets share the same
            // head and at least one of them has ended.
            return i1.hasNext() ? 1 : (i2.hasNext() ? -1 : 0);
        } else {
            return retVal;
        }
    }

    /**
     * Returns {@code true} iff the set <span style="font-style:italic;">A</span>
     * is a subset of <span style="font-style:italic;">B</span>.
     * <p><span style="font-weight:bold">Note</span>: this method uses the
     * natural order of the elements in the two sets (i.e.: it uses the
     * elements' {@link Comparable#compareTo(java.lang.Object)} methods). You
     * can contrast this method with the
     * {@link Sets#isSubset(java.util.SortedSet, java.util.SortedSet)}
     * method (which uses the two sets' comparators).</p>
     * <p><span style="font-weight:bold">Note 2</span>: this method will throw
     * an exception if the any of the two sets have a {@link SortedSet#comparator()
     * comparator}.</p>
     * @param <E>
     * @param A the first set.
     * @param B the second set.
     * @return {@code true} iff the set <span style="font-style:italic;">A</span>
     * is a subset of <span style="font-style:italic;">B</span>.
     */
    public static <E extends Comparable<? super E>> boolean isNaturalSubset(SortedSet<E> A, SortedSet<E> B) {
        if (A == null || A.isEmpty()) {
            return true;
        } else if (B == null || B.isEmpty() || A.size() > B.size()) {
            return false;
        } else {
            // The sets must not have a comparator! Because then the order could
            // be different and this method would not work.
            checkSetsOrderedNaturally(A, B);
            // None of the sets is null or empty.
            // The A will be a subset of B iff for every element in A we can
            // find one in B
            // Since the elements are ordered, we can simply iterate over them.
            Iterator<E> it1 = A.iterator();
            Iterator<E> it2 = B.tailSet(A.first()).iterator();
            while (it1.hasNext()) {
                E curEl1 = it1.next();
                // Now find in B the same element. We know that it will be one
                // of the 'next' elements.
                while (true) {
                    if (it2.hasNext()) {
                        int retVal = compare(curEl1, it2.next());
                        if (retVal == 0) {
                            // We have found the same element in the second set.
                            // Continue with the next element in the first set.
                            break;
                        } else if (retVal < 0) {
                            // The current element in A is smaller than the
                            // current element in B. There is no way we will be
                            // able to find the same element in B. This would
                            // mean that the next element in B should be
                            // smaller, which is an imposibility because of the
                            // increasing order.
                            return false;
                        }
                        // We haven't yet found the equal element in the second
                        // set. Continue searching.
                    } else {
                        // There are no elements in B anymore. B does not
                        // contain the current element from A.
                        return false;
                    }
                }
            }
            // We have gone through all elements in A and have found
            // corresponding ones in B. This means that A is indeed a subset of
            // B.
            return true;
        }
    }

    /**
     * Returns {@code true} iff the set <span style="font-style:italic;">A</span>
     * is a subset of <span style="font-style:italic;">B</span>.
     * <p><span style="font-weight:bold">Note</span>: this method uses the
     * {@link SortedSet#comparator() comparator} provided in the two sets. You
     * can contrast this method with the
     * {@link Sets#isNaturalSubset(java.util.SortedSet, java.util.SortedSet)}
     * method (which uses the elements' {@link
     * Comparable#compareTo(java.lang.Object)} methods).</p>
     * <p><span style="font-weight:bold">Note 2</span>: this method will throw
     * an exception if the two sets do not share the same comparator.</p>
     * @param <E>
     * @param A the first set.
     * @param B the second set.
     * @return {@code true} iff the set <span style="font-style:italic;">A</span>
     * is a subset of <span style="font-style:italic;">B</span>.
     */
    public static <E> boolean isSubset(SortedSet<E> A, SortedSet<E> B) {
        if (A == null || A.isEmpty()) {
            return true;
        } else if (B == null || B.isEmpty() || A.size() > B.size()) {
            return false;
        } else {
            Comparator<? super E> comparator = getElementComparator(A, B);
            // None of the sets is null or empty.
            // The A will be a subset of B iff for every element in A we can
            // find one in B
            // Since the elements are ordered, we can simply iterate over them.
            Iterator<E> it1 = A.iterator();
            Iterator<E> it2 = B.tailSet(A.first()).iterator();
            while (it1.hasNext()) {
                E curEl1 = it1.next();
                // Now find in B the same element. We know that it will be one
                // of the 'next' elements.
                while (true) {
                    if (it2.hasNext()) {
                        int retVal = comparator.compare(curEl1, it2.next());
                        if (retVal == 0) {
                            // We have found the same element in the second set.
                            // Continue with the next element in the first set.
                            break;
                        } else if (retVal < 0) {
                            // The current element in A is smaller than the
                            // current element in B. There is no way we will be
                            // able to find the same element in B. This would
                            // mean that the next element in B should be
                            // smaller, which is an imposibility because of the
                            // increasing order.
                            return false;
                        }
                        // We haven't yet found the equal element in the second
                        // set. Continue searching.
                    } else {
                        // There are no elements in B anymore. Thus B does not
                        // contain the current element from A.
                        return false;
                    }
                }
            }
            // We have gone through all elements in A and have found
            // corresponding ones in B. This means that A is indeed a subset of
            // B.
            return true;
        }
    }

    /**
     * Tests whether the given collections are both {@code null}, empty or
     * equal.
     * <p>It returns {@code true} if both collections are empty or {@code null},
     * otherwise it returns the value returned by {@code a.equals(b);}.</p>
     * @param a the first collection.
     * @param b the second collection.
     * @return {@code true} if both collections are empty or {@code null},
     * otherwise it returns the value returned by {@code a.equals(b);}.
     */
    public static boolean equal(Collection<?> a, Collection<?> b) {
        if (a == null) {
            return b == null || b.isEmpty();
        } else if (b == null) {
            return a.isEmpty();
        } else {
            return a.equals(b);
        }
    }

    /**
     * Returns {@code true} if and only if the intersection of {@code a} and {@code
     * b} is an empty set.
     * <p>Note: {@code null} is treated as an empty set.</p>
     * <p>Note: the complexity of this operation is O(M + N), where M and N are
     * the sizes of the sets {@code a} and {@code b}.</p>
     * <p><span style="font-weight:bold">Note</span>: this method uses the
     * {@link SortedSet#comparator() comparator} provided in the two sets. You
     * can contrast this method with the
     * {@link Sets#naturallyDisjoint(java.util.SortedSet, java.util.SortedSet)}
     * method (which uses the elements' {@link
     * Comparable#compareTo(java.lang.Object)} methods).</p>
     * <p><span style="font-weight:bold">Note</span>: this method will throw
     * an exception if the two sets do not share the same comparator.</p>
     * @param <E> the type of elements in the sets.
     * @param a the first set.
     * @param b the second set.
     * @return {@code true} if and only if the intersection of {@code a} and {@code
     * b} is an empty set.
     */
    public static <E> boolean disjoint(SortedSet<E> a, SortedSet<E> b) {
        if (a == null || a.isEmpty() || b == null || b.isEmpty()) {
            return true;
        } else {
            Comparator<? super E> comparator = getElementComparator(a, b);
            Iterator<E> it1 = a.iterator(), it2 = b.iterator();
            E curEl1 = it1.next(), curEl2 = it2.next();

            while (true) {
                int compare = comparator.compare(curEl1, curEl2);
                if (compare == 0) {
                    return false;
                } else if (compare < 0) {
                    if (it1.hasNext()) {
                        curEl1 = it1.next();
                    } else {
                        return true;
                    }
                } else {
                    if (it2.hasNext()) {
                        curEl2 = it2.next();
                    } else {
                        return true;
                    }
                }
            }
        }
    }

    /**
     * Returns {@code true} if and only if the intersection of {@code a} and {@code
     * b} is an empty set.
     * <p>Note: {@code null} is treated as an empty set.</p>
     * <p>Note: the complexity of this operation is O(M + N), where M and N are
     * the sizes of the sets {@code a} and {@code b}.</p>
     * <p><span style="font-weight:bold">Note</span>: this method uses the
     * natural order of the elements in the two sets (i.e.: it uses the
     * elements' {@link Comparable#compareTo(java.lang.Object)} methods). You
     * can contrast this method with the
     * {@link Sets#disjoint(java.util.SortedSet, java.util.SortedSet)}
     * method (which uses the two sets' comparators).</p>
     * <p><span style="font-weight:bold">Note</span>: this method will throw
     * an exception if the any of the two sets have a {@link SortedSet#comparator()
     * comparator}.</p>
     * @param <E> the type of elements in the sets.
     * @param a the first set.
     * @param b the second set.
     * @return {@code true} if and only if the intersection of {@code a} and {@code
     * b} is an empty set.
     */
    public static <E extends Comparable<? super E>> boolean naturallyDisjoint(SortedSet<E> a, SortedSet<E> b) {
        if (a == null || a.isEmpty() || b == null || b.isEmpty()) {
            return true;
        } else {
            // The sets must not have a comparator! Because then the order could
            // be different and this method would not work.
            checkSetsOrderedNaturally(a, b);
            
            Iterator<E> it1 = a.iterator(), it2 = b.iterator();
            E curEl1 = it1.next(), curEl2 = it2.next();

            while (true) {
                int compare = compare(curEl1, curEl2);
                if (compare == 0) {
                    return false;
                } else if (compare < 0) {
                    if (it1.hasNext()) {
                        curEl1 = it1.next();
                    } else {
                        return true;
                    }
                } else {
                    if (it2.hasNext()) {
                        curEl2 = it2.next();
                    } else {
                        return true;
                    }
                }
            }
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Printing">
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
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "output"));
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
     * output, "{", "}", ", ")</span>.
     * @param list the list whose elements to print to the given writer.
     * @param output the output where to write the elements to (may not be
     * {@code null}).
     * @throws IOException this exception is thrown if an error occurred while
     * writing to the output.
     */
    public static void printSet(Iterable<? extends Object> list, Writer output) throws IOException {
        print(list, output, "{", "}", ", ");
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private Sets() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    /**
     * This method works only if at least one of the given two sets is either
     * null or empty. It returns:
     *  <ul>
     *      <li>{@code -1} if the first set is null or empty but the second one
     *          isn't,</li>
     *      <li>{@code 0} if both sets are null or empty,</li>
     *      <li>{@code 1} if the second set is null or empty but the first one
     *          isn't, and</li>
     *      <li>{@code 2} if both sets are neither null nor empty.</li>
     *  </ul>
     * @param <E>
     * @param s1
     * @param s2
     * @return
     */
    private static <E> int nullOrEmptyCompare(SortedSet<E> s1, SortedSet<? extends E> s2) {
        if (s1 == s2) {
            // The sets are the same.
            return 0;
        } else if (s1 == null || s1.isEmpty()) {
            // If the first set is empty, then just check whether the second one
            // is too, otherwise the second one will be invariably greater then.
            return (s2 == null || s2.isEmpty()) ? 0 : -1;
        } else if (s2 == null || s2.isEmpty()) {
            // If the first set is not empty, but the second is then the latter
            // should compare lower to the first set
            return 1;
        } else {
            // Both sets are not empty. We have to compare them element-wise.
            // Return a code that indicates so.
            return 2;
        }
    }

    /**
     * Returns the element comparator for the two sets. This method makes sure
     * that the comparators of the two sets are the same and that they are not
     * null (otherwise it throws an exception).
     */
    private static <E> Comparator<? super E> getElementComparator(SortedSet<E> s1, SortedSet<? extends E> s2) throws IllegalArgumentException {
        Comparator<? super E> comparator = s1.comparator();
        if (!s2.comparator().equals(comparator)) {
            // Both of the sets provide comparators, but the two comparators
            // are not the same. This is an illegal situation.
            throw new IllegalArgumentException(i18n("ERR_SORTED_SETS_COMPARATORS_DIFFER"));
        } else if (comparator == null) {
            throw new IllegalArgumentException(i18n("ERR_SORTED_SETS_NO_COMPARATOR"));
        }
        return comparator;
    }

    /**
     * This method returns one of the following:
     *  <ul>
     *      <li>{@code 0} if both parameters are {@code null} or if they
     *          compare equal,</li>
     *      <li>{@code 1} if el1 is larger than el2, and</li>
     *      <li>{@code -1} if el1 is smaller than el2.</li>
     *  </ul>
     * @param <E>
     * @param el1
     * @param el2
     * @return
     */
    private static <E extends Comparable<? super E>> int compare(E el1, E el2) {
        // Compare the current two elements. If exactly one of them is
        // null, then use the other to compare them. If both are null,
        // consider them the same.
        if (el1 == null) {
            if (el2 == null) {
                return 0;
            } else {
                return Integer.signum(-el2.compareTo(el1));
            }
        } else {
            return Integer.signum(el1.compareTo(el2));
        }
    }

    /**
     * Checks whether the given sets are ordered naturally and throws an
     * exception if they are not.
     * <p>Note: This method expects that both sets are not {@code null}.</p>
     * @param <E>
     * @param s1
     * @param s2
     * @throws IllegalArgumentException
     */
    private static <E> void checkSetsOrderedNaturally(SortedSet<E> s1, SortedSet<? extends E> s2) throws IllegalArgumentException {
        if (s1.comparator() != null || s2.comparator() != null) {
            throw new IllegalArgumentException(i18n("ERR_SETS_NOT_NATURALLY_ORDERED"));
        }
    }
    // </editor-fold>
}
