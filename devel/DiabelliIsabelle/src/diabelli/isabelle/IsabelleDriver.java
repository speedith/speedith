/*
 * File name: IsabelleDriver.java
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
package diabelli.isabelle;

import diabelli.components.DiabelliComponent;
import diabelli.components.FormulaFormatsProvider;
import diabelli.components.util.BareGoalProvidingReasoner;
import diabelli.isabelle.pure.lib.TermYXML;
import diabelli.isabelle.terms.TermFormatDescriptor;
import diabelli.isabelle.terms.TermsToDiabelli;
import diabelli.logic.FormulaFormat;
import diabelli.logic.Goal;
import diabelli.logic.Goals;
import isabelle.Term.Term;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.logging.Level;
import javax.swing.Timer;
import org.isabelle.iapp.facade.CentralEventDispatcher;
import org.isabelle.iapp.facade.IAPP;
import org.isabelle.iapp.process.Message;
import org.isabelle.iapp.process.ProverManager;
import org.isabelle.iapp.process.features.InjectedCommands;
import org.isabelle.iapp.process.features.InjectionFinishListener;
import org.isabelle.iapp.process.features.InjectionResult;
import org.isabelle.iapp.process.features.InjectionResultListener;
import org.isabelle.iapp.proofdocument.StateChangeEvent;
import org.isabelle.iapp.proofdocument.StateListener;
import org.openide.util.Exceptions;
import org.openide.util.NbBundle;
import org.openide.util.lookup.ServiceProvider;
import org.openide.windows.TopComponent;

/**
 * This is the main class of the Isabelle driver for Diabelli. It provides
 * current Isabelle's goals to Diabelli and gives changed goals back to the
 * active Isabelle script.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@ServiceProvider(service = DiabelliComponent.class)
public class IsabelleDriver extends BareGoalProvidingReasoner implements FormulaFormatsProvider {

    //<editor-fold defaultstate="collapsed" desc="Fields">
    private IsabelleMessageListener isabelleListener;
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    public IsabelleDriver() {
        isabelleListener = new IsabelleMessageListener();
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="GoalProvidingReasoner Interface Implementation">
    @Override
    public String getName() {
        return org.openide.util.NbBundle.getBundle(IsabelleDriver.class).getString("ISA_DRIVER_NAME");
    }
    //</editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Formula Format Provider">
    @Override
    public Collection<FormulaFormat<?>> getFormulaFormats() {
        return FormulaFormatsContainer.IsabelleFormats;
    }
    
    private static class FormulaFormatsContainer {
        private static final List<FormulaFormat<?>> IsabelleFormats;
        
        static {
            ArrayList<FormulaFormat<?>> tmp = new ArrayList<>();
            tmp.add(TermFormatDescriptor.getInstance());
            IsabelleFormats = Collections.unmodifiableList(tmp);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Isabelle Goal-Change Monitoring">
    /**
     * Tries to fetch the current prover. It will throw an exception if the
     * prover could not have been obtained for any reason. <p>This prover is
     * needed to listen for messages from Isabelle to I3P.</p>
     *
     * @return the current prover instance. It never returns {@code null}, it
     * rather throws exceptions.
     * @throws IllegalStateException thrown if the prover instance could not
     * have been obtained for some reason.
     */
    @NbBundle.Messages({
        "ID_no_iapp=Could not obtain a communication channel with Isabelle.",
        "ID_no_prover=Could not obtain the prover interface to Isabelle."
    })
    public static ProverManager getProver() throws IllegalStateException {
        IAPP iapp = IAPP.getInstance();
        if (iapp == null) {
            throw new IllegalStateException(Bundle.ID_no_iapp());
        }
        ProverManager prover = iapp.getProver();
        if (prover == null) {
            throw new IllegalStateException(Bundle.ID_no_prover());
        }
        return prover;
    }

    /**
     * Issues an ML command to the prover and returns an injection result.
     * <p>You may wish to add an {@link InjectionResultListener} to the returned
     * {@link InjectionResult}. With this you will receive the response of the
     * prover.</p>
     *
     * @param cmd the ML command to be issued to the prover.
     * @return the <span style="font-style:italic;">future</span> result (the
     * answer of the prover).
     * @throws UnsupportedOperationException
     */
    @NbBundle.Messages({
        "ID_no_commands=Support for issuing commands to Isabelle is missing. This is needed to obtain goals from it."
    })
    public static InjectionResult executeCommand(String cmd) throws UnsupportedOperationException {
        ProverManager prover = IAPP.getInstance().getProver();
        InjectedCommands inj = prover.getFeature(InjectedCommands.class);
        if (inj == null) {
            throw new UnsupportedOperationException();
        }
        return inj.ML(null, cmd);
    }

    /**
     * This class listens for messages from Isabelle. There are plenty of
     * messages being exchanged all the time. This listener uses a delay
     * mechanism to prevent redundant goal updates when there is an onslaught of
     * messages and goals changes (for example, when the user tells Isabelle to
     * evaluate commands somewhere late in the theory file). This class receives
     * notifications of the completion of the request to Isabelle that it should
     * return current goals.
     */
    private class IsabelleMessageListener extends InjectionFinishListener implements StateListener, ActionListener, PropertyChangeListener {

        public static final String DIABELLI_ISABELLE_RESPONSE_GOAL = "DiabelliResponse: Goal: ";
        private static final String DIABELLI_ISABELLE_RESPONSE = "DiabelliResponse: ";
        private static final int DelayMillis = 500;
        private final Timer delayer;

        /**
         * <span style="font-weight:bold">Do not create new instances of this
         * class.</span> Use the one provided in {@link IsabelleDriver#isabelleListener}.
         */
        IsabelleMessageListener() {
            // Start listening for goal changes in Isabelle:
            CentralEventDispatcher centralEvents = IAPP.getInstance().getCentralEvents();
            centralEvents.addStateListener(this);
            TopComponent.getRegistry().addPropertyChangeListener(this);
            delayer = new Timer(DelayMillis, this);
            delayer.setRepeats(false);
            delayer.setCoalesce(true);
            delayer.setInitialDelay(DelayMillis);
        }

        /**
         * This is invoked by the ``delay timer'', which is started (and reset)
         * upon every {@link IsabelleMessageListener#stateChanged(org.isabelle.iapp.proofdocument.StateChangeEvent) state change event}.
         * The reason for delaying this action is to merge an avalanche of state
         * change events into a single request to Isabelle to give us its
         * current goals.
         *
         * @param e
         */
        @Override
        public void actionPerformed(ActionEvent e) {
            delayer.stop();
            fetchGoalsFromIsabelle();
        }

        /**
         * This method receives Isabelle's response, which gives us the YXML
         * format of the current goals in Isabelle.
         *
         * @param inj
         */
        @Override
        @NbBundle.Messages({
            "ID_isabelle_goals_not_obtained=Could not fetch the list of goals from Isabelle. A communication error occurred."
        })
        public void injectedFinished(InjectionResult inj) {
            try {
                Message[] results = inj.getResults();
                if (results != null) {
                    ArrayList<Goal> goals = new ArrayList<>();
                    for (Message message : results) {
                        if (message.getText() != null && message.getText().startsWith(DIABELLI_ISABELLE_RESPONSE_GOAL)) {
                            String escapedYXML = message.getText().substring(DIABELLI_ISABELLE_RESPONSE_GOAL.length());
                            String unescapedYXML = TermYXML.unescapeControlChars(escapedYXML);
                            Term term = TermYXML.parseYXML(unescapedYXML);
                            goals.add(TermsToDiabelli.toGoal(term));
                        }
                    }
                    setGoals(new Goals(goals));
                }
            } catch (InterruptedException ex) {
                throw new RuntimeException(Bundle.ID_isabelle_goals_not_obtained(), ex);
            }
        }

        /**
         * This method is invoked by I3P when the state of the Isabelle prover
         * changes. Typically, only user's interaction (like issuing commands
         * etc.) triggers an avalanche of state changes. After the avalanche is
         * over, no state changes should happen before another user-interaction.
         *
         * @param ev
         */
        @Override
        public void stateChanged(StateChangeEvent ev) {
            delayer.restart();
        }

        /**
         * Listens for TopComponent activations. It looks whether an I3P
         * Isabelle theory editor has been activated by the user (i.e., whether
         * the user has started editing an Isabelle theory editor).
         *
         * @param evt
         */
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if ("activated".equals(evt.getPropertyName())) {
                TopComponent activated = TopComponent.getRegistry().getActivated();
                if (activated instanceof org.isabelle.theoryeditor.TheoryEditor) {
                    requestActive();
                }
            }
        }
    }

    /**
     * Asks Isabelle to return all its current goals. Isabelle will return an
     * XML dump of the term trees.
     */
    private void fetchGoalsFromIsabelle() {
        try {
            InjectionResult cmd = executeCommand("GoalsExport.i3p_write_sds_goals ()");
            cmd.addInjectionResultListener(isabelleListener);
        } catch (UnsupportedOperationException uoex) {
            Exceptions.attachSeverity(uoex, Level.INFO);
        }
    }
    // </editor-fold>
}
