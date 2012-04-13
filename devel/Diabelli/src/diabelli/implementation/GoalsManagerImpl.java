/*
 * File name: GoalsManagerImpl.java
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
package diabelli.implementation;

import diabelli.Diabelli;
import diabelli.GoalsManager;
import diabelli.ReasonersManager;
import diabelli.components.GoalProvidingReasoner;
import static diabelli.implementation.Bundle.GM_reasoners_manager_null;
import static diabelli.implementation.Bundle.RM_diabelli_null;
import diabelli.logic.Goals;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.openide.util.NbBundle;

/**
 * The main implementation of the {@link GoalsManager Diabelli goal manager
 * specification}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
class GoalsManagerImpl implements GoalsManager {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private Goals currentGoals;
    private GoalsChangedListener goalsChangedListener;
    private final Diabelli diabelli;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     *
     * @param reasonersManager this goal manager will listen to this guy for
     * changes to the {@link ReasonersManager#getActiveReasoner() } property.
     */
    @NbBundle.Messages({
        "GM_reasoners_manager_null=A valid reasoners manager must be provided."
    })
    public GoalsManagerImpl(Diabelli diabelli, final ReasonersManager reasonersManager) {
        // TODO: Listen to activeReasoner changes...
        // TODO: Also listen to the goal changes of the currently active reasoner.
        if (reasonersManager == null) {
            throw new IllegalArgumentException(GM_reasoners_manager_null());
        }
        if (diabelli == null) {
            throw new IllegalArgumentException(RM_diabelli_null());
        }
        reasonersManager.addPropertyChangeListener(new ActiveReasonerChangedListener(reasonersManager), ReasonersManager.ActiveReasonerChangedEvent);
        this.diabelli = diabelli;
        goalsChangedListener = new GoalsChangedListener();
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="GoalsManager Interface Implementation">
    @Override
    public Goals getCurrentGoals() {
        return currentGoals;
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Property Changed Event Stuff">
    private void fireCurrentGoalsChangedEvent(Goals oldGoals) {
        pcs.firePropertyChange(CurrentGoalsChangedEvent, oldGoals, currentGoals);
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

    // <editor-fold defaultstate="collapsed" desc="Private Properties">
    private void setCurrentGoals(Goals goals) {
        if (goals != currentGoals) {
            Goals oldGoals = currentGoals;
            currentGoals = goals;
            Logger.getLogger(GoalsManagerImpl.class.getName()).log(Level.INFO, "Current goals have changed.");
            fireCurrentGoalsChangedEvent(oldGoals);
        }
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Goals Change Monitoring Stuff">
    private class ActiveReasonerChangedListener implements PropertyChangeListener {
        
        private final ReasonersManager reasonersManager;
        
        public ActiveReasonerChangedListener(ReasonersManager reasonersManager) {
            this.reasonersManager = reasonersManager;
        }
        
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            assert(evt.getOldValue() == null || evt.getOldValue() instanceof GoalProvidingReasoner);
            unregisterGoalsListener((GoalProvidingReasoner)evt.getOldValue());
            if (reasonersManager.getActiveReasoner() != null) {
                registerGoalsListener(reasonersManager.getActiveReasoner());
                setCurrentGoals(reasonersManager.getActiveReasoner().getGoals());
            } else {
                setCurrentGoals(null);
            }
        }
    }

    private class GoalsChangedListener implements PropertyChangeListener {

        public GoalsChangedListener() {
        }

        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            assert(evt.getNewValue() == null || evt.getNewValue() instanceof Goals);
            setCurrentGoals((Goals)evt.getNewValue());
        }
    }
    
    public void unregisterGoalsListener(GoalProvidingReasoner reasoner) {
        if (reasoner != null) {
            reasoner.removePropertyChangeListener(goalsChangedListener, GoalProvidingReasoner.CurrentGoalsChangedEvent);
        }
    }
    
    public void registerGoalsListener(GoalProvidingReasoner reasoner) {
        if (reasoner != null) {
            reasoner.addPropertyChangeListener(goalsChangedListener, GoalProvidingReasoner.CurrentGoalsChangedEvent);
        }
    }
    //</editor-fold>
}
