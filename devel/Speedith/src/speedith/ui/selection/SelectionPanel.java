/*
 *   Project: Speedith
 * 
 * File name: SelectionPanel.java
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
package speedith.ui.selection;

import speedith.core.reasoning.args.selection.SelectionSequence;
import speedith.ui.CirclesPanel2;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;
import javax.swing.DefaultListModel;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;
import static speedith.i18n.Translations.i18n;
import speedith.ui.SpiderDiagramClickEvent;
import speedith.core.reasoning.args.selection.SelectionStep;
import speedith.core.reasoning.args.selection.SelectionStep.SelectionRejectionExplanation;

/**
 * This is a GUI component that provides a step-by-step selection process on a
 * selected spider diagram.<p>This is useful for interactively providing
 * parameters for the application of an inference rule.</p> 
 * <p>{@link SelectionDialog The selection dialog} may be more convenient for
 * most use cases (as its use is quite straight-forward).</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SelectionPanel extends javax.swing.JPanel {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private SelectionSequenceMutable selection;
    private int curStep = -1;
    private final DefaultListModel selectionListModel = new DefaultListModel();
    private ArrayList<ActionListener> actionListeners;
    /**
     * This value is given as the {@link ActionEvent#getID() action ID} in the
     * {@link SelectionPanel#addActionListener(java.awt.event.ActionListener)
     * selection concluded event} if the user pressed on the <span
     * style="font-style:italic;">finish</span> button.
     */
    public final static int Finish = 0;
    /**
     * This value is given as the {@link ActionEvent#getID() action ID} in the
     * {@link SelectionPanel#addActionListener(java.awt.event.ActionListener)
     * selection concluded event} if the user pressed on the <span
     * style="font-style:italic;">finish</span> cancel.
     */
    public final static int Cancel = 1;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises the selection panel with no diagram and no selection steps.
     */
    public SelectionPanel() {
        initComponents();
        refreshUI();
    }

    /**
     * Initialises this selection panel with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this constructor makes a copy of
     * the given array.</p>
     *
     * @param diagram the diagram from which to select elements.
     * @param selectionSteps the selection steps this panel should display to
     * the user.
     */
    public SelectionPanel(SpiderDiagram diagram, SelectionStep... selectionSteps) {
        this(diagram, selectionSteps == null || selectionSteps.length == 0 ? null : new ArrayList<SelectionStep>(Arrays.asList(selectionSteps)));
    }

    /**
     * Initialises this selection panel with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this constructor makes a copy of
     * the given collection.</p>
     *
     * @param diagram the diagram from which to select elements.
     * @param selectionSteps the selection steps this panel should display to
     * the user.
     */
    public SelectionPanel(SpiderDiagram diagram, Collection<SelectionStep> selectionSteps) {
        this(diagram, selectionSteps == null || selectionSteps.isEmpty() ? null : new ArrayList<SelectionStep>(selectionSteps));
    }

    /**
     * Initialises this selection panel with the given selection steps. <p><span
     * style="font-weight:bold">Note</span>: this constructor does not make a
     * copy of the given array list.</p>
     *
     * @param diagram the diagram from which to select elements.
     * @param selectionSteps the selection steps this panel should display to
     * the user.
     */
    SelectionPanel(SpiderDiagram diagram, ArrayList<SelectionStep> selectionSteps) {
        initComponents();
        resetDiagramAndSelectionSteps(diagram, selectionSteps);
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Autogenerated Code">
    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        errorMessage = new javax.swing.JLabel();
        stepInstructionMessage = new javax.swing.JLabel();
        stepNumber = new javax.swing.JLabel();
        finishButton = new javax.swing.JButton();
        clearButton = new javax.swing.JButton();
        nextButton = new javax.swing.JButton();
        cancelButton = new javax.swing.JButton();
        previousButton = new javax.swing.JButton();
        diagramAndSelectionPanel = new javax.swing.JSplitPane();
        spiderDiagramPanel = new speedith.ui.SpiderDiagramPanel();
        selectionPanel = new javax.swing.JPanel();
        selectionLabel = new javax.swing.JLabel();
        javax.swing.JScrollPane jScrollPane1 = new javax.swing.JScrollPane();
        selectionList = new javax.swing.JList();

        errorMessage.setFont(new java.awt.Font("Dialog", 0, 12)); // NOI18N
        errorMessage.setForeground(new java.awt.Color(204, 0, 0));
        errorMessage.setText("* Error message...");

        stepInstructionMessage.setFont(new java.awt.Font("Dialog", 2, 12)); // NOI18N
        stepInstructionMessage.setText("Step instruction message...");

        stepNumber.setFont(new java.awt.Font("Dialog", 3, 12)); // NOI18N
        stepNumber.setText("Step 1 of 5: ");

        finishButton.setMnemonic(i18n("GSTR_FINISH_BUTTON_MNEMONIC").charAt(0));
        finishButton.setText(i18n("GSTR_FINISH_BUTTON_TEXT")); // NOI18N
        finishButton.setEnabled(false);
        finishButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                finishButtonActionPerformed(evt);
            }
        });

        clearButton.setMnemonic(i18n("GSTR_CLEAR_BUTTON_MNEMONIC").charAt(0));
        clearButton.setText(i18n("GSTR_CLEAR_BUTTON_TEXT")); // NOI18N
        clearButton.setToolTipText(i18n("SELSEQ_CLEAR_SELECTION")); // NOI18N
        clearButton.setEnabled(false);
        clearButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                clearButtonActionPerformed(evt);
            }
        });

        nextButton.setMnemonic(i18n("GSTR_NEXT_BUTTON_MNEMONIC").charAt(0));
        nextButton.setText(i18n("GSTR_NEXT_BUTTON_TEXT")); // NOI18N
        nextButton.setEnabled(false);
        nextButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                nextButtonActionPerformed(evt);
            }
        });

        cancelButton.setMnemonic(i18n("GSTR_CANCEL_BUTTON_MNEMONIC").charAt(0));
        cancelButton.setText(i18n("GSTR_CANCEL_BUTTON_TEXT")); // NOI18N
        cancelButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                cancelButtonActionPerformed(evt);
            }
        });

        previousButton.setMnemonic(i18n("GSTR_PREVIOUS_BUTTON_MNEMONIC").charAt(0));
        previousButton.setText(i18n("GSTR_PREVIOUS_BUTTON_TEXT")); // NOI18N
        previousButton.setEnabled(false);
        previousButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                previousButtonActionPerformed(evt);
            }
        });

        diagramAndSelectionPanel.setDividerLocation(500);
        diagramAndSelectionPanel.setDividerSize(5);

        spiderDiagramPanel.addSpiderDiagramClickListener(new speedith.ui.SpiderDiagramClickListener() {
            public void spiderDiagramClicked(speedith.ui.SpiderDiagramClickEvent evt) {
                onSpiderDiagramClicked(evt);
            }
        });
        diagramAndSelectionPanel.setLeftComponent(spiderDiagramPanel);

        selectionLabel.setText("Selection:");

        selectionList.setFont(new java.awt.Font("Dialog", 0, 12)); // NOI18N
        selectionList.setModel(selectionListModel);
        jScrollPane1.setViewportView(selectionList);

        javax.swing.GroupLayout selectionPanelLayout = new javax.swing.GroupLayout(selectionPanel);
        selectionPanel.setLayout(selectionPanelLayout);
        selectionPanelLayout.setHorizontalGroup(
            selectionPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(selectionPanelLayout.createSequentialGroup()
                .addGap(0, 0, 0)
                .addGroup(selectionPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(jScrollPane1, javax.swing.GroupLayout.PREFERRED_SIZE, 0, Short.MAX_VALUE)
                    .addComponent(selectionLabel, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
                .addGap(0, 0, 0))
        );
        selectionPanelLayout.setVerticalGroup(
            selectionPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(selectionPanelLayout.createSequentialGroup()
                .addComponent(selectionLabel)
                .addGap(3, 3, 3)
                .addComponent(jScrollPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 258, Short.MAX_VALUE)
                .addGap(0, 0, 0))
        );

        diagramAndSelectionPanel.setRightComponent(selectionPanel);

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addComponent(finishButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 123, Short.MAX_VALUE)
                .addComponent(previousButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(clearButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(nextButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(cancelButton))
            .addGroup(layout.createSequentialGroup()
                .addComponent(stepNumber)
                .addGap(1, 1, 1)
                .addComponent(stepInstructionMessage, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
            .addComponent(errorMessage, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
            .addComponent(diagramAndSelectionPanel, javax.swing.GroupLayout.PREFERRED_SIZE, 0, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addComponent(diagramAndSelectionPanel)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(errorMessage)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(stepNumber)
                    .addComponent(stepInstructionMessage))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(cancelButton)
                    .addComponent(nextButton)
                    .addComponent(clearButton)
                    .addComponent(finishButton)
                    .addComponent(previousButton)))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void finishButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_finishButtonActionPerformed
        fireSelectionEnd(Finish);
    }//GEN-LAST:event_finishButtonActionPerformed

    private void clearButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_clearButtonActionPerformed
        clearCurStepSelection(true, true);
    }//GEN-LAST:event_clearButtonActionPerformed

    private void nextButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_nextButtonActionPerformed
        goToNextStep(true, true);
    }//GEN-LAST:event_nextButtonActionPerformed

    private void cancelButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_cancelButtonActionPerformed
        fireSelectionEnd(Cancel);
    }//GEN-LAST:event_cancelButtonActionPerformed

    private void previousButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_previousButtonActionPerformed
        goToPreviousStep(true);
    }//GEN-LAST:event_previousButtonActionPerformed

    private void onSpiderDiagramClicked(speedith.ui.SpiderDiagramClickEvent evt) {//GEN-FIRST:event_onSpiderDiagramClicked
        SelectionStep curSelStep = getCurSelStep();
        if (curSelStep != null && getCurrentStep() >= 0 && getCurrentStep() < getStepCount()) {
            SelectionRejectionExplanation result = curSelStep.acceptSelection(evt.toRuleArg(), selection, getCurrentStep());
            if (result == null) {
                selection.addAcceptedClick(getCurrentStep(), evt, evt.toRuleArg());
                // Check if the step is finished. If it is, go to the next one:
                goToNextStep(false, false);
                refreshUI();
            } else {
                setErrorMsg(result.getExplanation());
            }
        }
    }//GEN-LAST:event_onSpiderDiagramClicked
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton cancelButton;
    private javax.swing.JButton clearButton;
    private javax.swing.JSplitPane diagramAndSelectionPanel;
    private javax.swing.JLabel errorMessage;
    private javax.swing.JButton finishButton;
    private javax.swing.JButton nextButton;
    private javax.swing.JButton previousButton;
    private javax.swing.JLabel selectionLabel;
    private javax.swing.JList selectionList;
    private javax.swing.JPanel selectionPanel;
    private speedith.ui.SpiderDiagramPanel spiderDiagramPanel;
    private javax.swing.JLabel stepInstructionMessage;
    private javax.swing.JLabel stepNumber;
    // End of variables declaration//GEN-END:variables
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the current selection.
     *
     * @return the current selection.
     */
    public SelectionSequence getSelection() {
        return selection;
    }

    /**
     * @return the index of the current step.
     */
    public int getCurrentStep() {
        return curStep;
    }

    /**
     * Returns the currently displayed diagram (the diagram from which the user
     * should choose elements).
     *
     * @return the currently displayed diagram (the diagram from which the user
     * should choose elements).
     */
    public SpiderDiagram getDiagram() {
        return this.spiderDiagramPanel.getDiagram();
    }

    /**
     * Sets the new diagram to be displayed (the diagram from which the user
     * should choose elements).
     *
     * @param diagram the new diagram to be displayed (the diagram from which
     * the user should choose elements).
     */
    public void setDiagram(SpiderDiagram diagram) {
        // Since we have changed the diagram, we also have to reset the current
        // selection (as there are no guarantees that the selection will remain
        // valid after the change of the diagram).
        selection.clearCurrentSelection();
        selection.setDiagram(diagram);
        resetDiagram(diagram, true);
    }

    /**
     * Returns the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     *
     * @return the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     */
    public List<SelectionStep> getSelectionSteps() {
        return getSelection().getSelectionSteps();
    }

    /**
     * Sets the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     *
     * @param steps the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     */
    public void setSelectionSteps(SelectionStep... steps) {
        resetSelectionSteps(new ArrayList<SelectionStep>(Arrays.asList(steps)), true);
    }

    /**
     * Sets the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     *
     * @param steps the selection steps that will guide the user through the
     * diagrammatic-element selection process.
     */
    public void setSelectionSteps(Collection<SelectionStep> steps) {
        resetSelectionSteps(new ArrayList<SelectionStep>(steps), true);
    }

    public void setDiagramAndSelectionSteps(SpiderDiagram diagram, Collection<? extends SelectionStep> steps) {
        resetDiagramAndSelectionSteps(diagram, new ArrayList<SelectionStep>(steps));
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Events">
    /**
     * Registers the given {@link ActionListener selection concluded
     * listener}. <p>This {@link ActionListener#actionPerformed(java.awt.event.ActionEvent)
     * event} is invoked whenever the user presses the <span
     * style="font-style:italic;">finish</span> or the <span
     * style="font-style:italic;">cancel</span> button.</p> <p>If the user
     * clicked <span style="font-style:italic;">cancel</span> then the
     * {@link ActionEvent#getID()} will be set to {@link SelectionPanel#Cancel}.
     * Otherwise, in case the user pressed the <span
     * style="font-style:italic;">finish</span> button, the ID will be set to
     * {@link SelectionPanel#Finish}.</p>
     *
     * @param l the event listener to register.
     */
    public void addActionListener(ActionListener l) {
        if (actionListeners == null) {
            actionListeners = new ArrayList<ActionListener>();
        }
        this.actionListeners.add(l);
    }

    /**
     * Removes the given {@link ActionListener selection concluded event listener}
     * from the selection concluded event. <p>The given listener will no longer
     * receive these events.</p>
     *
     * @param l the event listener to deregister.
     */
    public void removeActionListener(ActionListener l) {
        if (actionListeners != null) {
            actionListeners.remove(l);
        }
    }

    /**
     * Returns the array of all {@link SelectionPanel#addActionListener(ActionListener) registered}
     * {@link ActionListener selection concluded listeners}.
     *
     * @return the array of all {@link SelectionPanel#addActionListener(ActionListener) registered}
     * {@link ActionListener selection concluded listeners}.
     */
    public ActionListener[] getActionListeners() {
        return listenerList.getListeners(ActionListener.class);
    }

    protected final void fireSelectionEnd(int actionID) {
        if (actionListeners != null && actionListeners.size() > 0) {
            ActionEvent ae = new ActionEvent(this, actionID, null);
            for (ActionListener actionListener : actionListeners) {
                actionListener.actionPerformed(ae);
            }
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="UI Refresh Methods">
    private void refreshStepInstructionLabel() {
        if (selection == null
                || getCurrentStep() < 0
                || getCurrentStep() >= getStepCount()) {
            stepInstructionMessage.setText(null);
        } else {
            String instruction = selection.getSelectionStepAt(getCurrentStep()).getInstruction(selection, getCurrentStep());
            stepInstructionMessage.setText(instruction);
        }
    }

    private void refreshStepLabel() {
        if (getCurrentStep() >= getStepCount()) {
            stepNumber.setText(i18n("SELSEQ_STEP_FINISHED"));
        } else if (getStepCount() > 1) {
            stepNumber.setText(i18n("SELSEQ_STEP_N_OF_M", getCurrentStep() + 1, selection.getSelectionStepsCount()));
        } else {
            stepNumber.setText(null);
        }
    }

    private void refreshUI() {
        refreshAllButtons();
        refreshDiagramPanel();
        refreshAllLabels();
        refreshSelectionList();
    }

    private void resetDiagram(SpiderDiagram diagram, boolean resetUI) throws IllegalArgumentException {
        if (diagram == null) {
            throw new IllegalArgumentException("The argument 'diagram' must not be null.");
        }
        this.spiderDiagramPanel.setDiagram(diagram);
        if (resetUI) {
            resetCurStepAndUI();
        }
    }

    private void resetSelectionSteps(ArrayList<SelectionStep> selectionSteps, boolean resetUI) throws IllegalArgumentException {
        if (selectionSteps == null || selectionSteps.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "selectionSteps"));
        }
        // The collection of selection steps must not contain any null values.
        for (SelectionStep selectionStep : selectionSteps) {
            if (selectionStep == null) {
                throw new IllegalArgumentException(i18n("SELSEQ_NULL_STEPS"));
            }
        }
        this.selection = new SelectionSequenceMutable(getDiagram(), selectionSteps);
        if (resetUI) {
            resetCurStepAndUI();
        }
    }

    private void resetCurStepAndUI() {
        // Some extra initialisation:
        this.curStep = 0;
        initiateStep();
        refreshUI();
    }

    private void setErrorMsg(String msg) {
        if (msg == null || msg.isEmpty()) {
            errorMessage.setText(null);
        } else {
            errorMessage.setText(i18n("SELSEQ_ERROR_MSG", msg));
        }
    }

    private void refreshAllLabels() {
        refreshStepInstructionLabel();
        refreshStepLabel();
        setErrorMsg(null);
    }

    private void refreshAllButtons() {
        refreshNextButton();
        refreshPreviousButton();
        refreshFinishButton();
        refreshClearButton();
    }

    private void refreshNextButton() {
        nextButton.setEnabled(selection != null && getCurrentStep() < getStepCount() - 1 && getCurSelStep().isSkippable(selection, getCurrentStep()));
    }

    /**
     * The user can finish the selection only if all steps are skippable.
     */
    private void refreshFinishButton() {
        if (selection != null) {
            boolean canFinish = true;
            for (int i = getCurrentStep(); i < getStepCount(); i++) {
                SelectionStep selStep = selection.getSelectionStepAt(i);
                if (!selStep.isSkippable(selection, i) && !selStep.isFinished(selection, i)) {
                    canFinish = false;
                    break;
                }
            }
            finishButton.setEnabled(canFinish);
        } else {
            finishButton.setEnabled(false);
        }
    }

    private void refreshPreviousButton() {
        previousButton.setEnabled(selection != null && getCurrentStep() > 0);
    }

    private void refreshClearButton() {
        clearButton.setEnabled(selection != null && getCurSelStep() != null && selection.getAcceptedSelectionsCount(getCurrentStep()) > 0);
    }

    private void refreshDiagramPanel() {
        // Disable highlighting in the diagram, if the whole thing is finished:
        spiderDiagramPanel.setHighlightMode(getCurSelStep() == null || getCurrentStep() >= getStepCount() ? SelectionStep.None : getCurSelStep().getSelectableElements());
    }

    private void refreshSelectionList() {
        selectionListModel.clear();
        if (getCurSelStep() != null && selection.getAcceptedSelectionsCount(getCurrentStep()) > 0) {
            for (SpiderDiagramClickEvent selectedElement : selection.acceptedClicks[getCurrentStep()]) {
                selectionListModel.addElement(selectedElement.toString());
            }
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Internal Logic Methods">
    private void clearCurStepSelection(boolean force, boolean refreshUIIfChange) {
        // Check whether we should clean the selection on starting this step?
        SelectionStep curSelStep = getCurSelStep();
        if (curSelStep != null && (force || curSelStep.cleanSelectionOnStart())) {
            selection.clearCurrentSelection(getCurrentStep());
            if (refreshUIIfChange) {
                refreshUI();
            }
        }
    }

    private void goToNextStep(boolean skip, boolean refreshUIIfNext) {
        SelectionStep curSelStep = getCurSelStep();
        if (curSelStep != null && (skip || curSelStep.isFinished(selection, getCurrentStep()))) {
            ++curStep;
            clearCurStepSelection(false, false);
            initiateStep();
            if (refreshUIIfNext) {
                refreshUI();
            }
        }
    }

    private void goToPreviousStep(boolean refreshUIIfChange) {
        if (getCurrentStep() > 0) {
            --curStep;
            SelectionStep curSelStep = getCurSelStep();
            clearCurStepSelection(false, false);
            initiateStep();
            if (refreshUIIfChange) {
                refreshUI();
            }
        }
    }

    public void initiateStep() {
        SelectionStep curSelStep = getCurSelStep();
        if (curSelStep != null) {
            getCurSelStep().init(selection, getCurrentStep());
        }
    }

    /**
     * This method displays the diagram, sets the new selection steps and resets
     * the UI.
     *
     * @param diagram
     * @param selectionSteps
     * @throws IllegalArgumentException
     */
    private void resetDiagramAndSelectionSteps(SpiderDiagram diagram, ArrayList<SelectionStep> selectionSteps) throws IllegalArgumentException {
        resetDiagram(diagram, false);
        resetSelectionSteps(selectionSteps, false);
        resetCurStepAndUI();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Properties">
    private SelectionStep getCurSelStep() {
        return getCurrentStep() >= getStepCount() || getCurrentStep() < 0 || selection == null ? null : selection.getSelectionStepAt(getCurrentStep());
    }

    private int getStepCount() {
        return selection == null ? 0 : selection.getSelectionStepsCount();
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private static class SelectionSequenceMutable extends SelectionSequence {

        protected ArrayList<SpiderDiagramClickEvent>[] acceptedClicks;

        @SuppressWarnings("unchecked")
        public SelectionSequenceMutable(SpiderDiagram diagram, ArrayList<SelectionStep> selectionSteps) {
            super(diagram, selectionSteps);
            this.acceptedClicks = new ArrayList[selectionSteps.size()];
        }

        void addAcceptedClick(int stepIndex, SpiderDiagramClickEvent evt, RuleArg arg) {
            (acceptedSelections[stepIndex] == null
                    ? (acceptedSelections[stepIndex] = new ArrayList<RuleArg>())
                    : acceptedSelections[stepIndex]).add(arg);
            (acceptedClicks[stepIndex] == null
                    ? (acceptedClicks[stepIndex] = new ArrayList<SpiderDiagramClickEvent>())
                    : acceptedClicks[stepIndex]).add(evt);
        }

        void clearCurrentSelection(int stepIndex) {
            if (acceptedSelections[stepIndex] != null) {
                acceptedSelections[stepIndex].clear();
            }
            if (acceptedClicks[stepIndex] != null) {
                acceptedClicks[stepIndex].clear();
            }
        }
        
        void clearCurrentSelection() {
            Arrays.fill(acceptedClicks, null);
            Arrays.fill(acceptedSelections, null);
        }

        void setDiagram(SpiderDiagram diagram) {
            this.diagram = diagram;
        }
    }
    //</editor-fold>
}
