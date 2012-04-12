/*
 * File name: Goals.java
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
package diabelli.logic;

import diabelli.Diabelli;
import diabelli.GoalsManager;
import diabelli.components.GoalProvidingReasoner;
import java.util.*;

/**
 * Contains a set of goals that are provided by {@link GoalProvidingReasoner goal-providing
 * reasoners}. Use the {@link GoalsManager} in the {@link Diabelli} service to
 * find the currently active goals in Diabelli.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Goals implements Iterable<Goal> {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final ArrayList<Goal> goals;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new instance of goals. This constructor uses the given goals as
     * is (i.e., it stores the reference and does not make a copy before storing
     * it).
     *
     * @param goals the {@link Goals#getGoals() goals} contained in this
     * collection.
     */
    public Goals(ArrayList<Goal> goals) {
        this.goals = goals;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns an unmodifiable list of goals. This method returns {@code null}
     * if there are no goals present.
     *
     * @return an unmodifiable list of goals.
     */
    public List<Goal> getGoals() {
        return isEmpty() ? null : Collections.unmodifiableList(goals);
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Collections Interface Implementation">
    /**
     * Returns the number of goals in this collection.
     *
     * @return the number of goals in this collection.
     */
    public int size() {
        return isEmpty() ? 0 : goals.size();
    }

    /**
     * Indicates whether there are any goals in this goals collection.
     *
     * @return a value that indicates whether there are any goals in this goals
     * collection.
     */
    public boolean isEmpty() {
        return goals == null || goals.isEmpty();
    }

    /**
     * Checks whether the given goal is contained in this collection.
     *
     * @param goal the goal to search for.
     * @return {@code true} iff the given goal is contained in this collection.
     */
    public boolean contains(Goal goal) {
        return isEmpty() ? false : goals.contains(goal);
    }
    /**
     * Checks whether the given goals are contained in this collection.
     *
     * @param goals the goals to search for.
     * @return {@code true} iff the given goals are contained in this collection.
     */
    public boolean containsAll(Collection<? extends Goals> goals) {
        return isEmpty() ? false : this.goals.containsAll(goals);
    }

    /**
     * Returns an unmodifiable iterator of goals.
     * @return an unmodifiable iterator of goals.
     */
    @Override
    public Iterator<Goal> iterator() {
        return isEmpty() ? new EmptyIterator() : new GoalsIterator(goals.listIterator());
    }

    /**
     * Returns an unmodifiable list iterator of goals.
     * @return an unmodifiable list iterator of goals.
     */
    public ListIterator<Goal> listIterator() {
        return isEmpty() ? new EmptyIterator() : new GoalsIterator(goals.listIterator());
    }

    /**
     * Returns an array containing all the goals.
     * @return an array containing all the goals.
     */
    public Goal[] toArray() {
        return isEmpty() ? new Goal[0] : goals.toArray(new Goal[0]);
    }

    /**
     * Returns the goal at the given index.
     * @param index the index of the goal to get.
     * @return the goal at the given index.
     */
    public Goal get(int index) {
        if (isEmpty()) {
            throw new IndexOutOfBoundsException();
        } else {
            return goals.get(index);
        }
    }

    /**
     * Returns the index of the given goal.
     * @param goal the goal for which to look up the index.
     * @return the index of the given goal.
     */
    public int indexOf(Goal goal) {
        return isEmpty() ? -1 : goals.indexOf(goal);
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Iterator Implementations">
    private static class EmptyIterator implements ListIterator<Goal> {

        public EmptyIterator() {
        }

        @Override
        public boolean hasNext() {
            return false;
        }

        @Override
        public Goal next() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean hasPrevious() {
            return false;
        }

        @Override
        public Goal previous() {
            throw new UnsupportedOperationException();
        }

        @Override
        public int nextIndex() {
            throw new UnsupportedOperationException();
        }

        @Override
        public int previousIndex() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void set(Goal e) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void add(Goal e) {
            throw new UnsupportedOperationException();
        }
    }

    private static class GoalsIterator implements ListIterator<Goal> {

        private final ListIterator<Goal> origIter;

        public GoalsIterator(ListIterator<Goal> origIter) {
            this.origIter = origIter;
        }

        @Override
        public boolean hasNext() {
            return origIter.hasNext();
        }

        @Override
        public Goal next() {
            return origIter.next();
        }

        @Override
        public boolean hasPrevious() {
            return origIter.hasPrevious();
        }

        @Override
        public Goal previous() {
            return origIter.previous();
        }

        @Override
        public int nextIndex() {
            return origIter.nextIndex();
        }

        @Override
        public int previousIndex() {
            return origIter.previousIndex();
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void set(Goal e) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void add(Goal e) {
            throw new UnsupportedOperationException();
        }
    }
    //</editor-fold>
}
