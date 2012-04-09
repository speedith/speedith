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
import isabelle.*;
import isabelle.XML.Elem;
import isabelle.XML.Tree;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.Arrays;
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
import scala.Function1;
import scala.collection.immutable.List;

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

        public static final String DIABELLI_ISABELLE_RESPONSE_GOAL = "DiabelliResponse: Goal: ";
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
                        if (message.getText() != null && message.getText().startsWith(DIABELLI_ISABELLE_RESPONSE_GOAL)) {
                            String strangeXML = message.getText().substring(DIABELLI_ISABELLE_RESPONSE_GOAL.length());
                            String strangeXML2 = unembedControls(strangeXML);
                            final Tree tree = YXML.parse(strangeXML2);
                            isabelle.Term_XML$Decode$ a = new Term_XML$Decode$();
                            scala.collection.immutable.List<Tree> treeList = scala.collection.immutable.List.tabulate(0, new Function1<Integer, Tree>() {

                                @Override
                                public Tree apply(Integer t1) {
                                    return tree;
                                }

                                @Override
                                public <A> Function1<A, Tree> compose(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen(Function1<Tree, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public void apply$mcVI$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public boolean apply$mcZI$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public int apply$mcII$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public float apply$mcFI$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public long apply$mcLI$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public double apply$mcDI$sp(int i) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public void apply$mcVL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public boolean apply$mcZL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public int apply$mcIL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public float apply$mcFL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public long apply$mcLL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public double apply$mcDL$sp(long l) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public void apply$mcVF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public boolean apply$mcZF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public int apply$mcIF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public float apply$mcFF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public long apply$mcLF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public double apply$mcDF$sp(float f) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public void apply$mcVD$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public boolean apply$mcZD$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public int apply$mcID$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public float apply$mcFD$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public long apply$mcLD$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public double apply$mcDD$sp(double d) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Object> compose$mcVI$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Boolean> compose$mcZI$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Integer> compose$mcII$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Float> compose$mcFI$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Long> compose$mcLI$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Double> compose$mcDI$sp(Function1<A, Integer> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Object> compose$mcVL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Boolean> compose$mcZL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Integer> compose$mcIL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Float> compose$mcFL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Long> compose$mcLL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Double> compose$mcDL$sp(Function1<A, Long> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Object> compose$mcVF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Boolean> compose$mcZF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Integer> compose$mcIF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Float> compose$mcFF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Long> compose$mcLF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Double> compose$mcDF$sp(Function1<A, Float> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Object> compose$mcVD$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Boolean> compose$mcZD$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Integer> compose$mcID$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Float> compose$mcFD$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Long> compose$mcLD$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<A, Double> compose$mcDD$sp(Function1<A, Double> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcVI$sp(Function1<Object, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcZI$sp(Function1<Boolean, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcII$sp(Function1<Integer, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcFI$sp(Function1<Float, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcLI$sp(Function1<Long, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Integer, A> andThen$mcDI$sp(Function1<Double, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcVL$sp(Function1<Object, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcZL$sp(Function1<Boolean, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcIL$sp(Function1<Integer, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcFL$sp(Function1<Float, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcLL$sp(Function1<Long, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Long, A> andThen$mcDL$sp(Function1<Double, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcVF$sp(Function1<Object, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcZF$sp(Function1<Boolean, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcIF$sp(Function1<Integer, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcFF$sp(Function1<Float, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcLF$sp(Function1<Long, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Float, A> andThen$mcDF$sp(Function1<Double, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcVD$sp(Function1<Object, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcZD$sp(Function1<Boolean, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcID$sp(Function1<Integer, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcFD$sp(Function1<Float, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcLD$sp(Function1<Long, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }

                                @Override
                                public <A> Function1<Double, A> andThen$mcDD$sp(Function1<Double, A> fnctn) {
                                    throw new UnsupportedOperationException("Not supported yet.");
                                }
                            });
                            Term.Term t = a.term().apply(treeList);
                            Logger.getLogger(IsabelleMessageListener.class.getName()).log(Level.INFO, "WTF: {0}", t.toString());
                        }
                    }
                }
            } catch (InterruptedException ex) {
                throw new RuntimeException(Bundle.ID_isabelle_goals_not_obtained(), ex);
            }
        }
    }

    /**
     * Unembeds control characters from the embedded YXML string. Use this on
     * the YXML string before you pass it on to {@link YXML#parse(java.lang.CharSequence) }.
     * @param s the YXML string to unembed.
     * @return the unembedded version of the given YXML string.
     */
    @NbBundle.Messages({
        "ID_yxml_invalid_controls=The YXML string contains illegal embedded control characters."
    })
    public static String unembedControls(CharSequence s) {
        int length = s.length();
        StringBuilder sb = new StringBuilder(length);
        for (int i = 0; i < length; i++) {
            char c = s.charAt(i);
            if (c == 192) {
                i++;
                if (i < length) {
                    c = (char) (s.charAt(i) - 128);
                    if (c == 5 || c == 6) {
                        sb.append(c);
                    } else {
                        sb.append(s.charAt(i - 1)).append(s.charAt(i));
                    }
                } else {
                    sb.append(c);
                }
            } else {
                sb.append(c);
            }
        }
        return sb.toString();
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
