/*
 * File name: GoalProvidingReasoner.java
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
package diabelli.components;

import diabelli.logic.Goals;
import java.beans.PropertyChangeListener;

/**
 * Goal-providing reasoners are all interactive reasoners that fulfil the following
 * requirements: <ul> <li>they provide a list of goals that are to be proved
 * (these goals may be provided to the Diabelli framework in whatever format,
 * but the format should preferably be understandable by other Diabelli
 * components, which can then present these goals diagrammatically, for
 * example),</li> <li>the goals should contain premises and a conclusion (a goal
 * is proved if the premises entail the conclusion trivially), and</li> <li>if
 * the list of this prover's goals changes, Diabelli should be notified of it (through
 * events).</li> </ul>
 * 
 * <p>Note that a goal-providing reasoner alone does not have to accept changed
 * goals from other components. Goal-providing reasoners can use the Diabelli
 * framework merely for displaying goals in other ways (diagrammatic, for example)
 * or exporting them to other components. Reasoners that accept changed goals
 * are of the type {@link GoalAcceptingReasoner}.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface GoalProvidingReasoner extends Reasoner {
    /**
     * Returns this reasoner's current goals (the ones the user is currently
     * working with, for example, the goals of the current proof in the active editor
     * window).
     * @return this reasoner's current goals.
     */
    Goals getGoals();

    //<editor-fold defaultstate="collapsed" desc="Property Changed Stuff">
    /**
     * Registers a property listener. This manager provides the following
     * events: <ul><li>{@link GoalProvidingReasoner#CurrentGoalsChangedEvent}</li></ul>
     *
     * @param listener the object that will receive the property changed events.
     */
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    /**
     * Registers a property listener.
     *
     * @param listener the object that will receive the property changed events.
     * @param event the event to which the listener wants to be registered (see
     * {@link GoalProvidingReasoner#addPropertyChangeListener(java.beans.PropertyChangeListener)}
     * for a list of available events).
     */
    void addPropertyChangeListener(PropertyChangeListener listener, String event);
    
    /**
     * Unregisters the given property listener.
     *
     * @param listener the object that will not receive the property changed
     * events anymore.
     */
    void removePropertyChangeListener(PropertyChangeListener listener);
    
    /**
     * Unregisters the given property listener.
     *
     * @param listener the object that will not receive the property changed
     * events anymore.
     * @param event the event from which to deregister this listener.
     */
    void removePropertyChangeListener(PropertyChangeListener listener, String event);
    
    /**
     * The identifier that will come with the {@link GoalProvidingReasoner#addPropertyChangeListener(java.beans.PropertyChangeListener) property
     * change event} that indicates that the current goals have changed.
     */
    static final String CurrentGoalsChangedEvent = "current_goals_changed";
    //</editor-fold>
    
}
