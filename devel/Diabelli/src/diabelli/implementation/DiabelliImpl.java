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
import diabelli.FormulaFormatManager;
import diabelli.GoalsManager;
import diabelli.ReasonersManager;
import diabelli.components.DiabelliComponent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.openide.util.Lookup;
import org.openide.util.Lookup.Result;
import org.openide.util.LookupEvent;
import org.openide.util.LookupListener;
import org.openide.util.lookup.AbstractLookup;
import org.openide.util.lookup.InstanceContent;
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

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private final InstanceContent instanceContent;
    private Result<DiabelliComponent> lookupResult;
    private final AbstractLookup componentsLookup;
    private final HashSet<DiabelliComponent> components = new HashSet<DiabelliComponent>();
    private final ArrayList<ManagerInternals> managers = new ArrayList<ManagerInternals>();
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Managers Fields">
    private final ReasonersManagerImpl reasonersManager;
    private final GoalsManagerImpl goalManager;
    private final FormulaFormatManagerImpl formulaFormatManager;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructor">
    public DiabelliImpl() {
        Logger.getLogger(DiabelliImpl.class.getName()).log(Level.INFO, "Diabelli initialised.");

        // Initialise all managers:
        managers.add(reasonersManager = new ReasonersManagerImpl(this));
        managers.add(goalManager = new GoalsManagerImpl(this, reasonersManager));
        managers.add(formulaFormatManager = new FormulaFormatManagerImpl(this));

        // First create an empty list of components (then wait for them to
        // register or deregister).
        instanceContent = new InstanceContent();
        componentsLookup = new AbstractLookup(instanceContent);

        // Initialise the particular managers:
        for (ManagerInternals manager : managers) {
            manager.initialise();
        }

        // Find all Diabelli components and register them.
        lookupResult = Lookup.getDefault().lookupResult(DiabelliComponent.class);
        lookupResult.addLookupListener(new LookupListener() {

            @Override
            public void resultChanged(LookupEvent ev) {
                throw new UnsupportedOperationException("Registering/unregistering Diabelli drivers is not yet implemented.");
            }
        });
        updateComponentsList();

        // Now call the final stage in the initialisation of managers:
        for (ManagerInternals manager : managers) {
            manager.onAfterComponentsLoaded();
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Diabelli Interface Implementation">
    @Override
    public GoalsManager getGoalManager() {
        return goalManager;
    }

    @Override
    public ReasonersManager getReasonersManager() {
        return reasonersManager;
    }

    @Override
    public FormulaFormatManager getFormulaFormatManager() {
        return formulaFormatManager;
    }

    @Override
    public Set<? extends DiabelliComponent> getRegisteredComponents() {
        return Collections.unmodifiableSet(components);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Lookup Provider Implementation">
    @Override
    public Lookup getLookup() {
        // TODO: Check if we have to provide synchronisation here.
//        synchronized (instanceContent) {
//        if (lookupResult == null) {
        // Listen for Diabelli component registration (this will update the list
        // of components in Diabelli.
//        }
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
        components.clear();
        for (DiabelliComponent comp : comps) {
            instanceContent.add(comp);
            components.add(comp);
        }
    }
    // </editor-fold>
}
