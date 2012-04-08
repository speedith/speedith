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

import diabelli.Diabelli;
import diabelli.GoalsManager;
import diabelli.components.DiabelliComponent;
import diabelli.components.util.BareGoalProvidingReasoner;
import diabelli.logic.Goals;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.Timer;
import org.isabelle.iapp.facade.IAPP;
import org.isabelle.iapp.process.Message;
import org.isabelle.iapp.process.ProverManager;
import org.isabelle.iapp.process.ProverMessageListener;
import org.isabelle.iapp.process.features.InjectedCommands;
import org.isabelle.iapp.process.features.InjectionFinishListener;
import org.isabelle.iapp.process.features.InjectionResult;
import org.openide.util.Exceptions;
import org.openide.util.Lookup;
import org.openide.util.NbBundle;
import org.openide.util.lookup.ServiceProvider;

/**
 * This is the main class of the Isabelle driver for Diabelli. It provides
 * current Isabelle's goals to Diabelli and gives changed goals back to the
 * active Isabelle script.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@ServiceProvider(service = DiabelliComponent.class)
public class IsabelleDriver extends BareGoalProvidingReasoner {
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

    // <editor-fold defaultstate="collapsed" desc="Isabelle Monitoring">
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
     * Tries to obtain current goals from the Isabelle process.
     */
    private void fireFetchGoals() {
        try {
            InjectionResult cmd = executeCommand("GoalsExport.i3p_write_sds_goals ()");
            cmd.addInjectionResultListener(new IsabelleMessageListener());
        } catch (UnsupportedOperationException uoex) {
            Exceptions.attachSeverity(uoex, Level.INFO);
        }
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
    private class IsabelleMessageListener extends InjectionFinishListener implements ProverMessageListener, ActionListener {

        private static final String DIABELLI_ISABELLE_RESPONSE = "DiabelliResponse: ";
        private static final int DelayMillis = 500;
        private final Timer delayer;

        IsabelleMessageListener() {
            // Start listening for goal changes in Isabelle:
            getProver().addProverMessageListener(this);
            delayer = new Timer(DelayMillis, this);
        }

        @Override
        public void proverMessage(Message res) {
            synchronized (delayer) {
                // We've got to check that the message isn't a Diabelli
                // response. The thing is that we can get an endless loop of
                // goal-fetches if we don't ignore messages that are actually
                // responses to Diabelli. All responses to Diabelli have
                // the string "DiabelliResponse: " at the beginning.
                if (!res.getText().startsWith(DIABELLI_ISABELLE_RESPONSE)) {
                    delayer.restart();
                }
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            synchronized (delayer) {
                delayer.stop();
            }
            fetchGoalsFromIsabelle();
        }

        @Override
        @NbBundle.Messages({
            "ID_isabelle_goals_not_obtained=Could not fetch the list of goals from Isabelle. A communication error occurred."
        })
        public void injectedFinished(InjectionResult inj) {
            try {
                Message[] results = inj.getResults();
                if (results != null) {
                    for (Message message : results) {
                        Logger.getLogger(IsabelleMessageListener.class.getName()).log(Level.INFO, "Got the following reply from Isabelle: {0}", message.getText());
                    }
                }
            } catch (InterruptedException ex) {
                throw new RuntimeException(Bundle.ID_isabelle_goals_not_obtained(), ex);
            }
        }
    }

    /**
     * Asks Isabelle to return all its current goals. Isabelle will return an
     * XML dump of the term trees.
     */
    private void fetchGoalsFromIsabelle() {
        // TODO: Focus request should happen only when the user enters an Isabelle
        // editor...
        Diabelli diabelli = Lookup.getDefault().lookup(Diabelli.class);
        diabelli.getReasonersManager().requestActive(this);
        // Check for new goals (asynchronously)...
        fireFetchGoals();
    }
    // </editor-fold>
}
