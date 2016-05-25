package speedith.ui.selection;

import propity.util.Strings;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Goals;
import speedith.ui.SubgoalPanel;
import speedith.ui.SubgoalsPanel;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
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
public class SelectSubgoalDialog extends JDialog {
    private boolean cancelled = false;
    private SpiderDiagram selected;
    private int selectedIndex = 0;
    private List<SubgoalPanel> subgoals;
    private JPanel subgoalPanels ;

    public SelectSubgoalDialog(Frame owner, boolean modal, Goals goals) {
        super(owner, modal);
        subgoals = new ArrayList<>(goals.getGoalsCount());
        initComponents(goals);
        putGoalPanels(goals.getGoals());
    }

    private void initComponents(Goals goals) {

        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
        setModalityType(java.awt.Dialog.ModalityType.APPLICATION_MODAL);
        setTitle("Select Subgoal"); // NOI18N

        JScrollPane scrlGoals = new javax.swing.JScrollPane();
        scrlGoals.setBackground(new java.awt.Color(255, 255, 255));
        final JLabel errorText = new JLabel();
        errorText.setForeground(Color.RED);
        errorText.setText("");
        final JButton ok = new JButton();
        JButton cancel = new JButton();

        cancel.setText("Cancel");
        cancel.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                cancelled = true;
                dispose();
            }
        });
        ok.setText("OK");
        ok.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                if (selected == null) {
                    errorText.setText("Please select a subgoal");
                } else {
                    cancelled = false;
                    dispose();
                }
            }
        });

        subgoalPanels = new JPanel();
        subgoalPanels.setBackground(new java.awt.Color(255, 255, 255));
        subgoalPanels.setLayout(new java.awt.GridLayout(0,1));
        scrlGoals.setViewportView(subgoalPanels);
        subgoalPanels.setBorder(BorderFactory.createLineBorder(Color.BLUE));
        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
                layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                        .addComponent(scrlGoals, javax.swing.GroupLayout.DEFAULT_SIZE, 642, Short.MAX_VALUE)
                        .addComponent(errorText)
                        .addGroup(layout.createSequentialGroup().addComponent(ok).addComponent(cancel))
        );
        layout.setVerticalGroup(
                layout.createSequentialGroup()
                        .addComponent(scrlGoals, javax.swing.GroupLayout.DEFAULT_SIZE, 328, Short.MAX_VALUE)
                        .addGroup(layout.createParallelGroup(GroupLayout.Alignment.CENTER).addComponent(errorText))
                        .addGroup(layout.createParallelGroup().addComponent(ok).addComponent(cancel))
        );

    }

    private void putGoalPanels(java.util.List<SpiderDiagram> goals) {
        Dimension size = new Dimension();
        final int goalsCount = goals.size();
        // Display the spider diagrams together with their sub-goal index.
        for (int i = 0; i < goalsCount; i++) {
            final SpiderDiagram spiderDiagram = goals.get(i);
            final int index = i;
            GridBagConstraints bgc = new java.awt.GridBagConstraints();
            bgc.gridx = 0;
            bgc.fill = java.awt.GridBagConstraints.BOTH;
            bgc.weightx = 1.0;
            bgc.weighty = 1.0;
            final SubgoalPanel subgoalPanel = new SubgoalPanel();
            // If there is only one subgoal, don't display its subgoal index.
            // TODO: Rather create a function that hides the subgoal index.
            subgoalPanel.setSubgoalIndex(goalsCount > 1 ? i : -1);
            subgoalPanel.setDiagram(spiderDiagram);
            size.width = Math.max(size.width, subgoalPanel.getPreferredSize().width);
            size.height += subgoalPanel.getPreferredSize().height;
            subgoalPanels.add(subgoalPanel);
            subgoals.add(subgoalPanel);
            subgoalPanel.addMouseListener(new MouseListener() {
                final SpiderDiagram thisDiagram = spiderDiagram;
                final int thisIndex = index;
                @Override
                public void mouseClicked(MouseEvent mouseEvent) {
                    if (mouseEvent.getComponent() == subgoalPanel) {
                        for (SubgoalPanel s : subgoals) {
                            s.setBorder(BorderFactory.createEmptyBorder());
                        }
                        subgoalPanel.setBorder(BorderFactory.createLineBorder(Color.RED, 2));
                        selected = thisDiagram;
                        selectedIndex = thisIndex;
                  //      subgoalPanels.updateUI();
                        subgoalPanels.repaint();

                  //      getContentPane().repaint();
                  //      subgoalPanels.validate();
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
        // Calculate the preferred size of this panel.
       /* if (!Strings.isNullOrEmpty(pnlStepDescription.getDescription())) {
            size.height += STEP_DESCRIPTION_HEIGHT;
        }
        if (!Strings.isNullOrEmpty(pnlTitle.getTitle())) {
            size.height += SUBGOALS_TITLE_HEIGHT;
        }*/
        validate();
        setPreferredSize(size);
    }

    public SpiderDiagram getSelected() {
        return selected;
    }

    public int getSelectedIndex() {
        return selectedIndex;
    }

    public boolean isCancelled() {
        return cancelled;
    }
}
