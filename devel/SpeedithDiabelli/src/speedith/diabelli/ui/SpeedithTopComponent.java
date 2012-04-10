/*
 * File name: SpeedithTopComponent.java
 *    Author: matej
 * 
 *  Copyright © 2011 Matej Urbas
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
package speedith.diabelli.ui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.logging.Level;
import javax.swing.SwingUtilities;
import javax.swing.Timer;
import org.isabelle.iapp.facade.IAPP;
import org.isabelle.iapp.process.Message;
import org.isabelle.iapp.process.ProverManager;
import org.isabelle.iapp.process.ProverMessageListener;
import org.isabelle.iapp.process.features.InjectedCommands;
import org.isabelle.iapp.process.features.InjectionFinishListener;
import org.isabelle.iapp.process.features.InjectionResult;
import org.isabelle.iapp.process.features.InjectionResultListener;
import org.netbeans.api.settings.ConvertAsProperties;
import org.openide.awt.ActionID;
import org.openide.awt.ActionReference;
import org.openide.util.Exceptions;
import org.openide.util.NbBundle;
import org.openide.windows.TopComponent;
import speedith.core.lang.reader.ReadingException;
import static speedith.diabelli.ui.Translations.i18n;

/**
 * Top component which displays something.
 */
@ConvertAsProperties(dtd = "-//speedith.diabelli.ui//Speedith//EN", autostore = false)
@TopComponent.Description(preferredID = "SpeedithTopComponent", iconBase = "speedith/diabelli/ui/SpeedithIconVennDiagram-16.png")
@TopComponent.Registration(mode = "explorer", openAtStartup = true, position = 60)
@ActionID(category = "Window", id = "speedith.diabelli.ui.SpeedithTopComponent")
@ActionReference(path = "Menu/Window", position = 300)
@TopComponent.OpenActionRegistration(displayName = "#CTL_SpeedithAction", preferredID = "SpeedithTopComponent")
public class SpeedithTopComponent extends TopComponent {

    //<editor-fold defaultstate="collapsed" desc="Private Fields">
    private ProverMessageListenerImpl messageListener;
    /**
     * This delayer invokes a redraw of the spider diagram with a delay. This is
     * to prevent a ton of redraw operations.
     */
    private DiagramDrawDelayer delayer = new DiagramDrawDelayer();
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    public SpeedithTopComponent() {
        initComponents();
        setName(NbBundle.getMessage(SpeedithTopComponent.class, "CTL_SpeedithTopComponent"));
        setToolTipText(NbBundle.getMessage(SpeedithTopComponent.class, "HINT_SpeedithTopComponent"));
        putClientProperty(TopComponent.PROP_UNDOCKING_DISABLED, Boolean.TRUE);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Generated Code">
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        compoundSpiderDiagramPanel1 = new speedith.ui.SpiderDiagramPanel();

        setLayout(new java.awt.BorderLayout());

        try {
            compoundSpiderDiagramPanel1.setDiagramString(i18n("SpeedithTopComponent.compoundSpiderDiagramPanel1.diagramString_1")); // NOI18N
        } catch (speedith.core.lang.reader.ReadingException e1) {
            e1.printStackTrace();
        }
        add(compoundSpiderDiagramPanel1, java.awt.BorderLayout.CENTER);
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private speedith.ui.SpiderDiagramPanel compoundSpiderDiagramPanel1;
    // End of variables declaration//GEN-END:variables
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Overrides">
    @Override
    public void componentOpened() {
        unregisterMessageListener();
        registerMessageListener();
    }

    @Override
    public void componentClosed() {
        unregisterMessageListener();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Property Loading/Storing">
    void writeProperties(java.util.Properties p) {
        // better to version settings since initial version as advocated at
        // http://wiki.apidesign.org/wiki/PropertyFiles
        p.setProperty("version", "1.0");
        // TODO store your settings
    }

    void readProperties(java.util.Properties p) {
        String version = p.getProperty("version");
        // TODO read your settings according to their version
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    /**
     * This method removes the {@link SpeedithTopComponent#messageListener message listener}
     * from the current prover's set of message listeners.
     * <p>This method does not set the message listener to {@code null}.</p>
     */
    private void unregisterMessageListener() {
        if (messageListener != null) {
            getProver().removeProverMessageListener(messageListener);
        }
    }

    /**
     * Registers the {@link SpeedithTopComponent#messageListener message listener}
     * as one of the current prover's message listeners.
     * <p>This method initialises the message listener field if it has not yet been
     * initialised.</p>
     */
    private void registerMessageListener() {
        if (messageListener == null) {
            messageListener = new ProverMessageListenerImpl();
        }
        getProver().addProverMessageListener(messageListener);
    }

    /**
     * Tries to draw the current subgoal as a spider diagram.
     */
    private void fireDiagramDrawing() {
        // Ask Diabelli to give us the subgoals converted to spider diagram
        // string representation.
        try {
            InjectionResult cmd = executeCommand("Diabelli.i3p_write_sds_goals ()");
            cmd.addInjectionResultListener(new DiabelliGoalsFetcher());
        } catch (UnsupportedOperationException uoex) {
            Exceptions.attachSeverity(uoex, Level.INFO);
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Helper Classes">
    private class ProverMessageListenerImpl implements ProverMessageListener {

        public ProverMessageListenerImpl() {
        }

        @Override
        public void proverMessage(Message res) {
//            System.out.println("MATEJ: " + res.toString());
            delayer.poke();
        }
    }

    /**
     * This delayer invokes a redraw of the spider diagram with a delay. This is
     * to prevent a ton of redraw operations.
     */
    private class DiagramDrawDelayer implements ActionListener {

        /**
         * The delay in milliseconds with which to trigger the diagram redraw.
         */
        private static final int Delay = 500;
        private final Timer delayTimer;

        public DiagramDrawDelayer() {
            delayTimer = new Timer(Delay, this);
        }

        /**
         * This method starts a new delayed dispatch (by forgetting the previous
         * one).
         */
        public void poke() {
            synchronized (delayTimer) {
                delayTimer.restart();
            }
        }

        @Override
        public void actionPerformed(ActionEvent ae) {
            synchronized (delayTimer) {
                delayTimer.stop();
            }
//            fireDiagramDrawing();
        }
    }

    private class DiabelliGoalsFetcher extends InjectionFinishListener {

        public DiabelliGoalsFetcher() {
        }

        @Override
        public void injectedFinished(InjectionResult inj) {
            try {
                final Message[] results = inj.getResults();
                SwingUtilities.invokeLater(new DiagramDrawDispatcher(results));
//                for (Message message : inj.getResults()) {
//                    System.out.println(message.toString());
//                }
//                for (Message message : inj.getErrors()) {
//                    System.out.println(message.toString());
//                }
            } catch (InterruptedException ex) {
                Exceptions.printStackTrace(ex);
            }
        }

        class DiagramDrawDispatcher implements Runnable {

            private final Message[] results;

            public DiagramDrawDispatcher(Message[] results) {
                this.results = results;
            }

            @Override
            public void run() {
                try {
                    if (results != null && results.length > 1) {
                        compoundSpiderDiagramPanel1.setDiagramString(results[1].getText());
                    } else {
                        compoundSpiderDiagramPanel1.setDiagram(null);
                    }
                } catch (ReadingException ex) {
                    Exceptions.printStackTrace(ex);
                }
            }
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Static Utility Methods">
    /**
     * Tries to fetch the current prover. It will throw an exception if the
     * prover could not have been obtained for any reason.
     * <p>This prover is needed to listen for messages from Isabelle to I3P.</p>
     * @return the current prover instance. It never returns {@code null}, it
     * rather throws exceptions.
     * @throws IllegalStateException thrown if the prover instance could not
     * have been obtained for some reason.
     */
    public static ProverManager getProver() throws IllegalStateException {
        IAPP iapp = IAPP.getInstance();
        if (iapp == null) {
            throw new IllegalStateException(i18n("STC_NO_IAPP"));
        }
        ProverManager prover = iapp.getProver();
        if (prover == null) {
            throw new IllegalStateException(i18n("STC_NO_PROVER"));
        }
        return prover;
    }

    /**
     * Issues an ML command to the prover and returns an injection result.
     * <p>You may wish to add an {@link InjectionResultListener} to the returned
     * {@link InjectionResult}. With this you will receive the response of the
     * prover.</p>
     * @param cmd the ML command to be issued to the prover.
     * @return the <span style="font-style:italic;">future</span> result (the
     * answer of the prover).
     * @throws UnsupportedOperationException 
     */
    public static InjectionResult executeCommand(String cmd) throws UnsupportedOperationException {
        ProverManager prover = IAPP.getInstance().getProver();
        InjectedCommands inj = prover.getFeature(InjectedCommands.class);
        if (inj == null) {
            throw new UnsupportedOperationException(i18n("STC_NO_CMD_INJECTION"));
        }
        return inj.ML(null, cmd);
    }
    // </editor-fold>
}
