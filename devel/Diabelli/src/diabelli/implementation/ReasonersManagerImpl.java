/*
 * File name: Class.java
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
import diabelli.ReasonersManager;
import diabelli.components.DiabelliComponent;
import diabelli.components.GoalProvidingReasoner;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.openide.util.NbBundle;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@NbBundle.Messages({
    "Manager_diabelli_null=A valid Diabelli framework manager instance must be provided."
})
class ReasonersManagerImpl implements ReasonersManager, ManagerInternals {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private GoalProvidingReasoner activeReasoner;
    private Diabelli diabelli;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    ReasonersManagerImpl(Diabelli diabelli) {
        if (diabelli == null) {
            throw new IllegalArgumentException(Bundle.Manager_diabelli_null());
        }
        this.diabelli = diabelli;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="ReasonersManager Interface Implementation">
    @Override
    public GoalProvidingReasoner getActiveReasoner() {
        return activeReasoner;
    }

    @Override
    public void requestActive(GoalProvidingReasoner reasoner) {
        // TODO: Somewhen in the future we might want to check whether the
        // currently active reasoner is busy etc.
        Logger.getLogger(ReasonersManagerImpl.class.getName()).log(Level.INFO, "Reasoner ''{0}'' requested focus.", reasoner.getName());
        setActiveReasoner(reasoner);
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Properties">
    private void setActiveReasoner(GoalProvidingReasoner reasoner) {
        if (reasoner != activeReasoner) {
            GoalProvidingReasoner oldReasoner = activeReasoner;
            activeReasoner = reasoner;
            fireActiveReasonerChangedEvent(oldReasoner);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Property Changed Event Stuff">
    private void fireActiveReasonerChangedEvent(GoalProvidingReasoner oldReasoner) {
        pcs.firePropertyChange(ActiveReasonerChangedEvent, oldReasoner, activeReasoner);
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
    
    // <editor-fold defaultstate="collapsed" desc="Implementation Specifics">
    @Override
    public void initialise() {
    }

    @Override
    public void onAfterComponentsLoaded() {
        // Set the first goal providing reasoner as the active one:
        for (DiabelliComponent diabelliComponent : diabelli.getRegisteredComponents()) {
            if (diabelliComponent instanceof GoalProvidingReasoner) {
                requestActive((GoalProvidingReasoner)diabelliComponent);
                break;
            }
        }
    }
    // </editor-fold>
}
