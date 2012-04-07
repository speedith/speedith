/*
 * File name: DiabelliImpl.java
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
import diabelli.GoalManager;
import diabelli.ReasonersManager;
import diabelli.components.DiabelliComponent;
import diabelli.components.GoalProvidingReasoner;
import java.util.Collection;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.openide.util.Lookup;
import org.openide.util.Lookup.Item;
import org.openide.util.Lookup.Result;
import org.openide.util.LookupEvent;
import org.openide.util.LookupListener;
import org.openide.util.lookup.AbstractLookup;
import org.openide.util.lookup.InstanceContent;
import org.openide.util.lookup.ProxyLookup;
import org.openide.util.lookup.ServiceProvider;

/**
 * This is the main hub of the Diabelli framework. Reasoners can register
 * themselves here, currently opened standalone reasoners (the ones that host a
 * proof) can be found here, supporting reasoners (the ones which can apply
 * inference steps on goals or prove them outright, display goals, provide
 * formula input mechanisms etc.), currently pending goals in a proof of a
 * standalone reasoner etc.
 *
 * <p><span style="font-weight:bold">Note</span>: This class is a singleton,
 * access its only instance through the lookup API.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@ServiceProvider(service = Diabelli.class)
public final class DiabelliImpl implements Diabelli {

    // <editor-fold defaultstate="collapsed" desc="Managers">
    private GoalManager goalManager = new GoalManagerImpl();
    private final InstanceContent instanceContent;
    private Result<DiabelliComponent> lookupResult;
    private ReasonersManager reasonersManager = new ReasonersManagerImpl();
    private final AbstractLookup componentsLookup;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    public DiabelliImpl() {
        Logger.getLogger(DiabelliImpl.class.getName()).log(Level.INFO, "Diabelli initialised.");

        // First create an empty list of components (then wait for them to
        // register or deregister).
        instanceContent = new InstanceContent();
        componentsLookup = new AbstractLookup(instanceContent);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Diabelli Interface Implementation">
    @Override
    public GoalManager getGoalManager() {
        return goalManager;
    }

    @Override
    public ReasonersManager getReasonersManager() {
        return reasonersManager;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Lookup Provider Implementation">
    @Override
    public Lookup getLookup() {
        // TODO: Check if we have to provide synchronisation here.
//        synchronized (instanceContent) {
        if (lookupResult == null) {
            // Listen for Diabelli component registration (this will update the list
            // of components in Diabelli.
            lookupResult = Lookup.getDefault().lookupResult(DiabelliComponent.class);
            lookupResult.addLookupListener(new LookupListener() {

                @Override
                public void resultChanged(LookupEvent ev) {
                    throw new UnsupportedOperationException("Registering/unregistering Diabelli drivers is not yet implemented.");
                }
            });
            updateComponentsList();
        }
//        }
        return componentsLookup;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Overrides">
    @Override
    public String toString() {
        return "Diabelli is awesome!";
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Components Registration">
    private void updateComponentsList() {
        Collection<? extends DiabelliComponent> comps = lookupResult.allInstances();
        for (DiabelliComponent comp : comps) {
            Logger.getLogger(DiabelliImpl.class.getName()).log(Level.INFO, "Found registered component: {0}", comp.getName());
            instanceContent.add(comp);
        }
    }
    // </editor-fold>
}
