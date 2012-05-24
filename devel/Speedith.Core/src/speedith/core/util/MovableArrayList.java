/*
 *   Project: Speedith.Core
 * 
 * File name: MovableArrayList.java
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

import java.util.*;

/**
 * This is a wrapper class that wraps a single {@link ArrayList} and delegates
 * all its operations to it.
 *
 * <p>One important difference between this container and the {@link ArrayList}
 * is that this class provides methods {@link MovableArrayList#moveTo(speedith.core.util.MovableArrayList)
 * }
 * and {@link MovableArrayList#swapWith(speedith.core.util.MovableArrayList) }
 * which either move the backing array list from this instance to the other or
 * swaps the backing array (both in O(1)).</p>
 *
 * <p>This class does not provide a way to get or change the backing array list
 * in any other way. This (together with the move-functionality described above)
 * provides a way to safely pass ownership of array lists to other classes,
 * which can properly encapsulate the reference without fear for
 * reference-escape.</p>
 *
 * <p><span style="font-weight:bold">Important</span>: this class is not
 * thread-safe. Wrapping it into {@link Collections#synchronizedList(java.util.List) a synchronised wrapper}
 * helps only if no {@link MovableArrayList#swapWith(speedith.core.util.MovableArrayList) swapping}
 * or {@link MovableArrayList#moveTo(speedith.core.util.MovableArrayList) moving}
 * is performed (as this may change the backing array while it is being accessed
 * in any way).</p>
 * 
 * <p>TODO: the {@link MovableArrayList#iterator() }, {@link MovableArrayList#listIterator()},
 * and {@link MovableArrayList#listIterator(int) } all leak a reference to the
 * backing array. What should we do?
 * 
 * <ul>
 * 
 * <li>Create wrappers for iterators and make them read-only?</li>
 * 
 * <li>Wrap the backing array into an unmodifiable list first and then return
 * the iterator?</li>
 * 
 * </ul>
 * 
 * </p>
 *
 * @param <E> the type of elements stored in this collection.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class MovableArrayList<E> implements List<E>, RandomAccess {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private ArrayList<E> store;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    public MovableArrayList() {
        store = new ArrayList<E>();
    }

    public MovableArrayList(Collection<? extends E> c) {
        store = new ArrayList<E>(c);
    }

    public MovableArrayList(int initialCapacity) {
        store = new ArrayList<E>(initialCapacity);
    }

    public MovableArrayList(MovableArrayList<? extends E> c) {
        store = new ArrayList<E>(c);
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Move Semantics">
    /**
     * Moves the contents (the backing array) of this list to {@code destination}.
     * 
     * <p>This collection will be empty after this operation finishes.</p>
     *
     * <p><span style="font-weight:bold">Important</span>: this method is not
     * thread-safe.</p>
     * 
     * @param destination
     */
    public void moveTo(MovableArrayList<? super E> destination) {
        move(this, destination);
    }

    /**
     * Swaps the backing array of this list with the one in {@code other}.
     *
     * <p><span style="font-weight:bold">Important</span>: this method is not
     * thread-safe.</p>
     * 
     * @param other the other list with which to swap contents.
     */
    public void swapWith(MovableArrayList<E> other) {
        swap(this, other);
    }

    /**
     * This method moves the backing array of {@code source} to {@code destination}.
     *
     * <p>Additionally, {@code source}'s backing array is initialised with a new
     * empty {@link ArrayList}.</p>
     *
     * <p><span style="font-weight:bold">Important</span>: this method is not
     * thread-safe.</p>
     *
     * @param <TSource> the type of elements stored in {@code source}.
     * @param <TDestination> the type of elements stored in {@code destination}.
     * @param source the collection from which to remove the backing array and
     * put it into {@code destination}.
     * @param destination the collection of which the old backing array will be
     * forfeited and replaced by the backing array of {@code source}.
     */
    public static <TDestination> void move(
            MovableArrayList<? extends TDestination> source,
            MovableArrayList<TDestination> destination) {
        @SuppressWarnings("unchecked")
        ArrayList<TDestination> tmp = (ArrayList<TDestination>) source.store;
        source.store = new ArrayList<>();
        destination.store = tmp;
    }

    /**
     * This method swaps the backing array of {@code source} with the one of
     * {@code destination} (in O(1)).
     *
     * <p><span style="font-weight:bold">Important</span>: this method is not
     * thread-safe.</p>
     *
     * @param <E> the type of elements stored involved collections.
     * @param a the first collection.
     * @param b the second collection.
     */
    public static <E> void swap(MovableArrayList<E> a, MovableArrayList<E> b) {
        ArrayList<E> tmpA = a.store;
        a.store = b.store;
        b.store = tmpA;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="List implementation">
    @Override
    public int size() {
        return store.size();
    }

    @Override
    public boolean isEmpty() {
        return store.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return store.contains(o);
    }

    /**
     * This method leaks a reference to the backing array! What to do?
     * 
     * See TODO note in class documentation.
     * 
     * @return 
     */
    @Override
    public Iterator<E> iterator() {
        return store.iterator();
    }

    @Override
    public Object[] toArray() {
        return store.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return store.toArray(a);
    }

    @Override
    public boolean add(E e) {
        return store.add(e);
    }

    @Override
    public boolean remove(Object o) {
        return store.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return store.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends E> c) {
        return store.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        return store.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return store.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return store.retainAll(c);
    }

    @Override
    public void clear() {
        store.clear();
    }

    @Override
    public E get(int index) {
        return store.get(index);
    }

    @Override
    public E set(int index, E element) {
        return store.set(index, element);
    }

    @Override
    public void add(int index, E element) {
        store.add(index, element);
    }

    @Override
    public E remove(int index) {
        return store.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return store.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return store.lastIndexOf(o);
    }

    /**
     * This method leaks a reference to the backing array! What to do?
     * 
     * See TODO note in class documentation.
     * 
     * @param index
     * @return 
     */
    @Override
    public ListIterator<E> listIterator() {
        return store.listIterator();
    }

    /**
     * This method leaks a reference to the backing array! What to do?
     * 
     * See TODO note in class documentation.
     * 
     * @param index
     * @return 
     */
    @Override
    public ListIterator<E> listIterator(int index) {
        return store.listIterator(index);
    }

    @Override
    public List<E> subList(int fromIndex, int toIndex) {
        return store.subList(fromIndex, toIndex);
    }
    //</editor-fold>
}
