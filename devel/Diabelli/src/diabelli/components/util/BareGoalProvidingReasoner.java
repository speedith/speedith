/*
 * File name: BareGoalProvidingReasoner.java
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
package diabelli.components.util;

import diabelli.components.GoalProvidingReasoner;
import diabelli.logic.Goals;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

/**
 * Provides a <span style="font-style:italic;">bare</span> (partial and convenience)
 * implementation of the {@link GoalProvidingReasoner} interface.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class BareGoalProvidingReasoner implements GoalProvidingReasoner {
    
    // <editor-fold defaultstate="collapsed" desc="Fields">
    private Goals goals;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    @Override
    public Goals getGoals() {
        return goals;
    }
    //</editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Protected Properties">
    /**
     * Sets the goals and fires the goals changed event if the new goals differ
     * from the current ones.
     * @param goals the new goals to be set.
     */
    protected void setGoals(Goals goals) {
        if (this.goals != goals) {
            Goals oldGoals = this.goals;
            this.goals = goals;
            fireCurrentGoalsChangedEvent(oldGoals);
        }
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Property Changed Event Stuff">
    protected void fireCurrentGoalsChangedEvent(Goals oldGoals) {
        pcs.firePropertyChange(CurrentGoalsChangedEvent, oldGoals, goals);
    }

    @Override
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        pcs.addPropertyChangeListener(listener);
    }

    @Override
    public void addPropertyChangeListener(PropertyChangeListener listener, String event) {
        pcs.addPropertyChangeListener(event, listener);
    }

    @Override
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        pcs.removePropertyChangeListener(listener);
    }

    @Override
    public void removePropertyChangeListener(PropertyChangeListener listener, String event) {
        pcs.removePropertyChangeListener(event, listener);
    }
    private PropertyChangeSupport pcs = new PropertyChangeSupport(this);
    // </editor-fold>
}
