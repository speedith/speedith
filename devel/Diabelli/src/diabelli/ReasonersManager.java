/*
 * File name: ReasonersManager.java
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
package diabelli;

import diabelli.components.GoalProvidingReasoner;
import diabelli.components.Reasoner;
import java.beans.PropertyChangeListener;
import org.openide.util.Lookup;

/**
 * Manages currently registered {@link Reasoner reasoners}. For example, this
 * manager tracks which {@link GoalProvidingReasoner goal-providing
 * reasoner} is currently active (if any). The goals of the currently active
 * goal-providing reasoner are available in the {@link Diabelli#getGoalManager()
 * goal manager}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface ReasonersManager {

    /**
     * Returns the currently active goal-providing reasoner, if any. This method
     * returns {@code null} if there is currently no active goal-providing
     * reasoner. Reasoners can request to become active via {@link
     * ReasonersManager#requestActive(diabelli.components.GoalProvidingReasoner)}.
     *
     * @return the currently active goal-providing reasoner, if any.
     */
    GoalProvidingReasoner getActiveReasoner();

    /**
     * This method tells the {@link Diabelli#getReasonersManager()
     * reasoners manager} to make the given {@link GoalProvidingReasoner} the
     * active one. In turn, this will put its goals into the {@link
     * Diabelli#getGoalManager() goals manager}.
     *
     * <p><span style="font-weight:bold">Note</span>: the reasoner should be in
     * the list of all reasoners, otherwise an {@link IllegalArgumentException}
     * is thrown.</p>
     *
     * @param reasoner the reasoner that should become the active one.
     */
    void requestActive(GoalProvidingReasoner reasoner);

    //<editor-fold defaultstate="collapsed" desc="Property Changed Stuff">
    /**
     * Registers a property listener. This manager provides the following
     * events: <ul><li>{@link ReasonersManager#ActiveReasonerChangedEvent}</li></ul>
     *
     * @param listener the object that will receive the property changed events.
     */
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    /**
     * Registers a property listener.
     *
     * @param listener the object that will receive the property changed events.
     * @param event the event to which the listener wants to be registered (see
     * {@link ReasonersManager#addPropertyChangeListener(java.beans.PropertyChangeListener)}
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
     * The identifier that will come with the {@link ReasonersManager#addPropertyChangeListener(java.beans.PropertyChangeListener) property
     * change event} that indicates that the active reasoner has changed.
     */
    static final String ActiveReasonerChangedEvent = "active_reasoner_changed";
    //</editor-fold>
}
