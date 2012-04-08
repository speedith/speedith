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

import diabelli.ReasonersManager;
import diabelli.components.GoalProvidingReasoner;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
class ReasonersManagerImpl implements ReasonersManager {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private GoalProvidingReasoner activeReasoner;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    public ReasonersManagerImpl() {
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
}
