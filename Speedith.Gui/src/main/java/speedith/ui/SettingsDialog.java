package speedith.ui;

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.automatic.AutomaticProver;
import speedith.core.reasoning.automatic.AutomaticProverProvider;
import speedith.core.reasoning.automatic.AutomaticProvers;
import speedith.core.reasoning.automatic.strategies.Strategies;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.strategies.StrategyProvider;

import javax.swing.*;
import javax.swing.event.ListDataListener;
import javax.swing.plaf.TabbedPaneUI;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Arrays;
import java.util.Set;
import java.util.prefs.Preferences;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class SettingsDialog  extends javax.swing.JDialog {

    private JTabbedPane settingsTab;

    private JPanel autoProverPanel;
    private JLabel typeLabel;
    private JLabel strategyLabel;
    private JComboBox typeCombo;
    private JComboBox strategyCombo;
    private JButton okButton;

    private JPanel settingsPanel;
    private JPanel diagramsPanel;
    private JComboBox diagramTypeCombo;


    public SettingsDialog(java.awt.Frame parent, boolean modal) {
        super(parent, modal);
        initComponents();
    }

    private void initComponents() {
        settingsPanel = new JPanel();
        okButton = new JButton();
        autoProverPanel = new JPanel();
        settingsTab = new JTabbedPane();
        typeLabel = new JLabel();
        typeCombo = new JComboBox(getProverComboList());
        strategyLabel = new JLabel();
        strategyCombo = new JComboBox(getStrategyComboList());

        diagramsPanel = new JPanel();
        diagramTypeCombo = new JComboBox(getDiagramTypesComboList());

        javax.swing.GroupLayout groupLayout;

        groupLayout = new javax.swing.GroupLayout(diagramsPanel);
        diagramsPanel.setLayout(groupLayout);
        groupLayout.setAutoCreateContainerGaps(true);
        groupLayout.setHorizontalGroup(groupLayout.createSequentialGroup().addComponent(diagramTypeCombo));
        groupLayout.setVerticalGroup(groupLayout.createSequentialGroup().addComponent(diagramTypeCombo,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE));
        settingsTab.addTab("Diagram Type", diagramsPanel);


        typeLabel.setText("Type");
        strategyLabel.setText("Strategy");

        groupLayout = new javax.swing.GroupLayout(autoProverPanel);
        autoProverPanel.setLayout(groupLayout);
        autoProverPanel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        groupLayout.setAutoCreateContainerGaps(true);
        groupLayout.setHorizontalGroup(
                groupLayout.createSequentialGroup()
                        .addGroup(
                                groupLayout.createParallelGroup()
                                        .addComponent(typeLabel)
                                        .addComponent(strategyLabel))
                        .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                        .addGroup(
                                groupLayout.createParallelGroup()
                                        .addComponent(typeCombo)
                                        .addComponent(strategyCombo)));
        groupLayout.setVerticalGroup(groupLayout.createSequentialGroup()
                .addGroup(groupLayout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(typeLabel).addComponent(typeCombo,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                        GroupLayout.PREFERRED_SIZE))
                .addGroup(groupLayout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(strategyLabel).addComponent(strategyCombo,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                        GroupLayout.PREFERRED_SIZE)));


        settingsTab.addTab("Auto Prover", autoProverPanel);




        okButton.setText("Ok");
        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                okbuttonClicked(actionEvent);
            }
        });

        JSeparator sep = new JSeparator();

        groupLayout = new javax.swing.GroupLayout(settingsPanel);
        settingsPanel.setLayout(groupLayout);
        groupLayout.setAutoCreateContainerGaps(false);
        groupLayout.setHorizontalGroup(groupLayout.createParallelGroup()
                .addComponent(settingsTab).addComponent(sep)
                .addGroup(groupLayout.createSequentialGroup().addContainerGap().addComponent(okButton)));
        groupLayout.setVerticalGroup(
                groupLayout.createSequentialGroup()
                        .addComponent(settingsTab)
                        .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED,
                     GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(sep,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                                GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(okButton)
                        .addContainerGap());
        getContentPane().add(settingsPanel, BorderLayout.CENTER);

        pack();
    }

    private void okbuttonClicked(ActionEvent actionEvent) {
        Preferences prefs =  Preferences.userNodeForPackage(SettingsDialog.class);
        ProverListItem selectedProver = (ProverListItem) typeCombo.getSelectedItem();
        prefs.put(AutomaticProvers.prover_preference, selectedProver.getAutomaticProverProvider().getAutomaticProverName());
        StrategyListItem selectedStrategy = (StrategyListItem) strategyCombo.getSelectedItem();
        prefs.put(Strategies.strategy_preference, selectedStrategy.getStrategyProvider().getStrategyName());
        DiagramType diagrams = (DiagramType) diagramTypeCombo.getSelectedItem();
        prefs.put(InferenceRules.diagram_type_preference, diagrams.name());
        dispose();
    }

    private ComboBoxModel getProverComboList() {
        Set<String> provers = AutomaticProvers.getKnownAutomaticProvers();
        ProverListItem[] proverItems = new ProverListItem[provers.size()];
        int i = 0;
        for (String providerName : provers) {
            proverItems[i++] = new ProverListItem(AutomaticProvers.getProvider(providerName));
        }
        Arrays.sort(proverItems);
        ComboBoxModel model = new DefaultComboBoxModel<>(proverItems);
        Preferences prefs = Preferences.userNodeForPackage(SettingsDialog.class);
        String prover = prefs.get(AutomaticProvers.prover_preference, null);
        if (prover != null) {
            model.setSelectedItem(new ProverListItem(AutomaticProvers.getProvider(prover)));
        }
        return model;
    }

    public AutomaticProver getSelectedProver() {
        ProverListItem selected = (ProverListItem) typeCombo.getSelectedItem();
        return selected.getAutomaticProverProvider().getAutomaticProver();
    }

    private ComboBoxModel getStrategyComboList() {
        Set<String> strategies = Strategies.getKnownStrategies();
        StrategyListItem[] stragetyItems = new StrategyListItem[strategies.size()];
        int i = 0;
        for (String strategyName : strategies) {
            stragetyItems[i++] = new StrategyListItem(Strategies.getProvider(strategyName));
        }
        Arrays.sort(stragetyItems);
        ComboBoxModel model = new DefaultComboBoxModel<>(stragetyItems);
        Preferences prefs = Preferences.userNodeForPackage(SettingsDialog.class);
        String selected = prefs.get(Strategies.strategy_preference, null);
        if (selected != null) {
            model.setSelectedItem(new StrategyListItem(Strategies.getProvider(selected)));
        }
        return model;
    }

    public Strategy getSelectedStrategy() {
        StrategyListItem selected = (StrategyListItem) strategyCombo.getSelectedItem();
        return selected.getStrategyProvider().getStrategy();
    }

    private ComboBoxModel<DiagramType> getDiagramTypesComboList() {
        ComboBoxModel<DiagramType> model = new DefaultComboBoxModel<>(DiagramType.values());
        Preferences prefs = Preferences.userNodeForPackage(SettingsDialog.class);
        String selected = prefs.get(InferenceRules.diagram_type_preference, null);
        if (selected != null) {
            model.setSelectedItem(DiagramType.valueOf(selected));
        }
        return model;
    }

    public DiagramType getSelectedDiagramType() {
        return (DiagramType) diagramTypeCombo.getSelectedItem();
    }

    private static class ProverListItem implements Comparable<ProverListItem> {

        private final AutomaticProverProvider proverProvider;

        public ProverListItem(AutomaticProverProvider provider) {
            if (provider == null) {
                throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "provider"));
            }
            this.proverProvider = provider;
        }

        public AutomaticProverProvider getAutomaticProverProvider() {
            return proverProvider;
        }

        @Override
        public String toString() {
            return proverProvider.getPrettyName();
        }

        @Override
        public int compareTo(ProverListItem o) {
            return proverProvider.toString().compareToIgnoreCase(o.toString());
        }
    }

    private static class StrategyListItem implements Comparable<StrategyListItem> {

        private final StrategyProvider strategyProvider;

        public StrategyListItem(StrategyProvider provider) {
            if (provider == null) {
                throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "provider"));
            }
            this.strategyProvider = provider;
        }

        public StrategyProvider  getStrategyProvider() {
            return strategyProvider;
        }

        @Override
        public String toString() {
            return strategyProvider.getPrettyName();
        }

        @Override
        public int compareTo(StrategyListItem o) {
            return strategyProvider.toString().compareToIgnoreCase(o.toString());
        }
    }
}
