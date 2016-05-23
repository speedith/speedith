/*
 *   Project: Speedith.Core
 * 
 * File name: Goals.java
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
package speedith.core.reasoning;

import speedith.core.lang.SpiderDiagram;

import java.io.Serializable;
import java.util.*;

import static speedith.core.i18n.Translations.i18n;

/**
 * This class contains a list of spider diagrams.
 * <p>This list represents the goals that have to be proved in a {@link Proof}
 * by applying {@link InferenceRule inference rules} on them.</p>
 * <p>Instances of this class (and its derived classes) are immutable.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Goals implements Serializable {

    private static final long serialVersionUID = -5994853267156830447L;
    private final ArrayList<SpiderDiagram> goals;

    /**
     * Initialises an instance of this class with a list of spider diagrams (the
     * goals/proof obligations).
     * <p>This constructor makes a copy of the given list. See {@link Goals#createGoalsFrom(java.util.List)}
     * and {@link Goals#createGoalsFrom(speedith.core.lang.SpiderDiagram[])} for
     * way of creating an instance of Goals without making a copy of the list.
     * Be warned, however, that you <span style="font-weight:bold">must not</span>
     * change the contents of the list of spider diagrams afterwards or you
     * risk erroneous behaviour.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     */
    public Goals(Collection<SpiderDiagram> goals) {
        this(goals == null || goals.isEmpty() ? null : new ArrayList<>(goals));
    }

    /**
     * Initialises an instance of this class with a list of spider diagrams (the
     * goals/proof obligations).
     * <p><span style="font-weight:bold">Warning</span>: this method does not
     * make a copy of the list. Make sure you do not change the contents of the
     * list afterwards.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     */
    Goals(ArrayList<SpiderDiagram> goals) {
        this.goals = goals;
    }

    /**
     * Initialises an instance of this class with a list of spider diagrams (the
     * goals/proof obligations).
     * <p><span style="font-weight:bold">Warning</span>: this method does not
     * make a copy of the list. Make sure you do not change the contents of the
     * list afterwards.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     */
    Goals(SpiderDiagram[] goals) {
        this(goals == null || goals.length < 1 ? null : Arrays.asList(goals));
    }

    /**
     * Returns an unmodifiable list of spider diagrams that represent the proof
     * goals (proof obligations).
     * <p>Note: this method may return {@code null} to indicate that there are
     * not goals (proof obligations) left.</p>
     *
     * @return an unmodifiable list of spider diagrams that represent the proof
     *         goals (proof obligations).
     *         <p>Note: this method may return {@code null} to indicate that there are
     *         not goals (proof obligations) left.</p>
     */
    @SuppressWarnings("ReturnOfCollectionOrArrayField")
    public List<SpiderDiagram> getGoals() {
        return (goals == null || goals.isEmpty()) ? null : Collections.unmodifiableList(goals);
    }

    /**
     * Returns the spider diagram goal (proof obligation) at the given index.
     * <p>Note: you should check the number of goals before calling this
     * function.</p>
     * <p>To iterate over goals, see the method {@link Goals#getGoals()}.</p>
     *
     * @param index the index of the goal to return.
     * @return a spider diagram (the goal at the given index).
     */
    public SpiderDiagram getGoalAt(int index) {
        if (goals == null) {
            throw new IndexOutOfBoundsException(i18n("GERR_INDEX_OUT_OF_BOUNDS"));
        }
        return goals.get(index);
    }

    /**
     * Returns the number of goals in this list.
     *
     * @return the number of goals in this list.
     */
    public int getGoalsCount() {
        return goals == null || goals.isEmpty() ? 0 : goals.size();
    }

    /**
     * Indicates whether this collection of goals is empty.
     *
     * @return a flag that indicates whether this collection of goals is empty.
     */
    public boolean isEmpty() {
        return goals == null || goals.isEmpty();
    }

    /**
     * Creates a new instance of the {@link Goals} class with the given list of
     * spider diagrams as the proof goals (proof obligations).
     * <p><span style="font-weight:bold">Warning</span>: this method does not
     * make a copy of the list. Make sure you do not change the contents of the
     * list afterwards.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     * @return the new instance of the {@link Goals} class.
     */
    public static Goals createGoalsFrom(List<SpiderDiagram> goals) {
        return new Goals(goals);
    }

    /**
     * Creates a new instance of the {@link Goals} class with the given list of
     * spider diagrams as the proof goals (proof obligations).
     * <p><span style="font-weight:bold">Warning</span>: this method does not
     * make a copy of the list. Make sure you do not change the contents of the
     * list afterwards.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     * @return the new instance of the {@link Goals} class.
     */
    public static Goals createGoalsFrom(SpiderDiagram... goals) {
        return new Goals(goals);
    }

    /**
     * Creates a new instance of the {@link Goals} class with the given list of
     * spider diagrams as the proof goals (proof obligations).
     * <p><span style="font-weight:bold">Warning</span>: this method does not
     * make a copy of the list. Make sure you do not change the contents of the
     * list afterwards.</p>
     * <p><span style="font-weight:bold">Note</span>: this is a bit of an unsafe
     * method. Use it with care.</p>
     *
     * @param goals the list of spider diagrams which represent the proof goals
     *              (proof obligations).
     * @return the new instance of the {@link Goals} class.
     */
    public static Goals createGoalsFrom(ArrayList<SpiderDiagram> goals) {
        return new Goals(goals);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Goals goals1 = (Goals) o;

        return !(goals != null ? !goals.equals(goals1.goals) : goals1.goals != null);
    }

    @Override
    public int hashCode() {
        return goals != null ? goals.hashCode() : 0;
    }

    @Override
    public String toString() {
        return "Goals(" + goals + ')';
    }
}
