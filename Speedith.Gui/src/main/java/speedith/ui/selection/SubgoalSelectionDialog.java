package speedith.ui.selection;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.RuleApplication;
import speedith.ui.SubgoalPanel;
import speedith.ui.SubgoalsPanel;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.*;
import java.util.List;

import static speedith.i18n.Translations.i18n;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
@Deprecated
public class SubgoalSelectionDialog extends JDialog {

    private boolean cancelled = true;

    private JPanel listOfSubGoals;
    private List<SubgoalsPanel> subgoals;
    private SpiderDiagram selected;
    private JButton btnOk;
    private JButton btnCancel;

    private JScrollPane spInputText;

    public SubgoalSelectionDialog(Frame owner, boolean modal) {
        super(owner, modal);
        subgoals = new ArrayList<>();
        initComponents();
    }

    private void initComponents() {
        listOfSubGoals= new JPanel();
        btnOk = new JButton();
        btnCancel = new JButton();

        listOfSubGoals.setBackground(new java.awt.Color(255, 255, 255));
        listOfSubGoals.setLayout(new java.awt.GridBagLayout());
        spInputText = new javax.swing.JScrollPane();
        spInputText.setViewportView(listOfSubGoals);
        setTitle("Choose the subgoal to save");


        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
        java.util.ResourceBundle bundle = java.util.ResourceBundle.getBundle("speedith/i18n/strings"); // NOI18N
        btnOk.setMnemonic(java.util.ResourceBundle.getBundle("speedith/i18n/strings").getString("TEXT_INPUT_DIALOG_OK_MNEMONIC").charAt(0));
        btnOk.setText(bundle.getString("TEXT_INPUT_DIALOG_OK")); // NOI18N
        btnOk.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnOkActionPerformed(evt);
            }
        });


        btnCancel.setMnemonic(java.util.ResourceBundle.getBundle("speedith/i18n/strings").getString("TEXT_INPUT_DIALOG_CANCEL_MNEMONIC").charAt(0));
        btnCancel.setText(bundle.getString("TEXT_INPUT_DIALOG_CANCEL")); // NOI18N
        btnCancel.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnCancelActionPerformed(evt);
            }
        });
        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
                layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                        .addGroup(layout.createSequentialGroup()
                                .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                                .addComponent(btnOk)
                                .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                                .addComponent(btnCancel))

                        .addComponent(spInputText, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 995, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(layout.createSequentialGroup().addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                        .addComponent(spInputText, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 406, Short.MAX_VALUE))
                        .addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(btnOk).addComponent(btnCancel))
        );

        pack();
    }

    private void btnCancelActionPerformed(ActionEvent evt) {
        dispose();
    }

    private void btnOkActionPerformed(ActionEvent evt) {
        cancelled = false;
        dispose();
    }


    public void setSubgoals(final java.util.List<Goals> goals, List<RuleApplication> ruleApplications) {
        for(int stepIndex = 0; stepIndex < goals.size(); stepIndex++) {
            final Goals g = goals.get(stepIndex);
            String goalTitle ;
            String stepDescription;

            if (stepIndex < 1) {
                goalTitle = i18n("PROOF_PANEL_INIT_GOAL_TITLE");
            } else {
                goalTitle =  i18n("PROOF_PANEL_GOAL_TITLE", stepIndex);
            }
            if (stepIndex < 1) {
                stepDescription = null;
            } else {
                stepDescription = i18n("PROOF_PANEL_STEP_DESC_GENERAL", ruleApplications.get(stepIndex - 1).getInferenceRule().getProvider().getPrettyName());
            }
            final SubgoalsPanel select = new SubgoalsPanel(g, goalTitle, stepDescription, Color.GRAY);

            GridBagConstraints bgc = new java.awt.GridBagConstraints();
            bgc.gridx = 0;
            bgc.fill = java.awt.GridBagConstraints.BOTH;
            bgc.weightx = 1.0;
            bgc.weighty = 1.0;
            listOfSubGoals.add(select, bgc);
            subgoals.add(select);
            if (!g.isEmpty()) {
                select.addMouseListener(new MouseListener() {
                    private Goals goal = g;

                    @Override
                    public void mouseClicked(MouseEvent mouseEvent) {
                       if (mouseEvent.getComponent() == select) {
                           for (SubgoalsPanel s : subgoals) {
                               s.setBorder(BorderFactory.createEmptyBorder());
                               s.setTitleBackground(Color.GRAY);
                           }
                           select.setTitleBackground(Color.RED);
                           select.setBorder(BorderFactory.createLineBorder(Color.RED, 2));
                           selected = goal.getGoalAt(0);
                           listOfSubGoals.repaint();
                       }
                    }


                    @Override
                    public void mousePressed(MouseEvent mouseEvent) {
                    }

                    @Override
                    public void mouseReleased(MouseEvent mouseEvent) {
                    }

                    @Override
                    public void mouseEntered(MouseEvent mouseEvent) {
                    }

                    @Override
                    public void mouseExited(MouseEvent mouseEvent) {
                    }
                });
            }

        }
        pack();

    }

    public boolean isCancelled() {
        return cancelled;
    }

    public SpiderDiagram getSelected() {
        return selected;
    }
}
