package speedith.ui;

import speedith.core.lang.DiagramType;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.automatic.AutomaticProver;
import speedith.core.reasoning.automatic.AutomaticProverProvider;
import speedith.core.reasoning.automatic.AutomaticProvers;
import speedith.core.reasoning.automatic.strategies.Strategies;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.strategies.StrategyProvider;
import speedith.core.reasoning.tactical.Tactics;
import speedith.ui.automatic.AutomaticProverThread;

import javax.swing.*;
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

    private static final long serialVersionUID = 7227563068597417669L;

    private JComboBox<ProverListItem> typeCombo;
    private JComboBox<StrategyListItem> strategyCombo;
    private JComboBox<DiagramType> diagramTypeCombo;
    private JCheckBox backgroundSearchCheckbox = new JCheckBox();
    private JCheckBox levelCheckbox = new JCheckBox();

    public SettingsDialog(java.awt.Frame parent, boolean modal) {
        super(parent, modal);
        initComponents();
    }

    private void initComponents() {
        this.setTitle("Preferences");
        JPanel settingsPanel = new JPanel();
        JButton okButton = new JButton();
        JPanel autoProverPanel = new JPanel();
        JTabbedPane settingsTab = new JTabbedPane();
        JLabel typeLabel = new JLabel();
        JLabel strategyLabel = new JLabel();
        JPanel diagramsPanel = new JPanel();
        JPanel tacticsPanel  = new JPanel();
        JLabel levelLabel = new JLabel();

        JLabel backgroundSearchLabel = new JLabel();
        final JLabel explanationLabel = new JLabel();
        final JLabel strategyExplanationLabel = new JLabel();




        javax.swing.GroupLayout groupLayout;

        typeCombo = new JComboBox<>(getProverComboList());
        strategyCombo = new JComboBox<>(getStrategyComboList());
        diagramTypeCombo = new JComboBox<>(getDiagramTypesComboList());

        typeCombo.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                ProverListItem item = (ProverListItem) typeCombo.getSelectedItem();
                explanationLabel.setText(item.getAutomaticProverProvider().getDescription());
            }
        });
        strategyCombo.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                StrategyListItem item = (StrategyListItem) strategyCombo.getSelectedItem();
                strategyExplanationLabel.setText(item.getStrategyProvider().getDescription());
            }
        });


        groupLayout = new javax.swing.GroupLayout(diagramsPanel);
        diagramsPanel.setLayout(groupLayout);
        groupLayout.setAutoCreateContainerGaps(true);
        groupLayout.setHorizontalGroup(groupLayout.createSequentialGroup().addComponent(diagramTypeCombo));
        groupLayout.setVerticalGroup(groupLayout.createSequentialGroup().addComponent(diagramTypeCombo,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE));
        settingsTab.addTab("Diagram Type", diagramsPanel);


        levelLabel.setText("Show low-level tactics");
        levelCheckbox.setSelected(getShowLowLevelTactics());
        groupLayout = new javax.swing.GroupLayout(tacticsPanel);
        tacticsPanel.setLayout(groupLayout);
        tacticsPanel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        groupLayout.setAutoCreateGaps(true);
        groupLayout.setHorizontalGroup(groupLayout.createSequentialGroup().addComponent(levelLabel,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE).addComponent(levelCheckbox,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE));
        groupLayout.setVerticalGroup(groupLayout.createParallelGroup().addComponent(levelLabel,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE).addComponent(levelCheckbox,GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                GroupLayout.PREFERRED_SIZE));
        settingsTab.addTab("Tactics", tacticsPanel);



        backgroundSearchCheckbox.setSelected(getBackGroundSearchEnabled());
        typeLabel.setText("Type");
        strategyLabel.setText("Strategy");
        backgroundSearchLabel.setText("Enable automatic proof search in the background");
        ProverListItem item = (ProverListItem) typeCombo.getSelectedItem();
        explanationLabel.setText(item.getAutomaticProverProvider().getDescription());
        StrategyListItem item2 = (StrategyListItem) strategyCombo.getSelectedItem();
        strategyExplanationLabel.setText(item2.getStrategyProvider().getDescription());



        groupLayout = new javax.swing.GroupLayout(autoProverPanel);
        autoProverPanel.setLayout(groupLayout);
        autoProverPanel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        groupLayout.setAutoCreateContainerGaps(true);
        groupLayout.setHorizontalGroup(
                groupLayout.createSequentialGroup()
                        .addGroup(
                                groupLayout.createParallelGroup()
                                        .addComponent(typeLabel)
                                        .addComponent(strategyLabel)
                                        .addComponent(backgroundSearchLabel))

                        .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                        .addGroup(
                                groupLayout.createParallelGroup()
                                        .addComponent(typeCombo)
                                        .addComponent(explanationLabel)
                                        .addComponent(strategyCombo)
                                        .addComponent(strategyExplanationLabel)
                                        .addComponent(backgroundSearchCheckbox))
        );
        groupLayout.setVerticalGroup(groupLayout.createSequentialGroup()
                .addGroup(groupLayout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(typeLabel).addComponent(typeCombo, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                        GroupLayout.PREFERRED_SIZE))
                .addComponent(explanationLabel)
                .addGroup(groupLayout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(strategyLabel).addComponent(strategyCombo, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                        GroupLayout.PREFERRED_SIZE))
                .addComponent(strategyExplanationLabel)
                .addGroup(groupLayout.createParallelGroup(GroupLayout.Alignment.BASELINE).addComponent(backgroundSearchLabel).addComponent(backgroundSearchCheckbox, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE,
                        GroupLayout.PREFERRED_SIZE))
        );


        settingsTab.addTab("Auto Prover", autoProverPanel);




        okButton.setText("Ok");
        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                okbuttonClicked();
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

    private void okbuttonClicked() {
        Preferences prefs =  Preferences.userNodeForPackage(SettingsDialog.class);
        ProverListItem selectedProver = (ProverListItem) typeCombo.getSelectedItem();
        prefs.put(AutomaticProvers.prover_preference, selectedProver.getAutomaticProverProvider().getAutomaticProverName());
        StrategyListItem selectedStrategy = (StrategyListItem) strategyCombo.getSelectedItem();
        prefs.put(Strategies.strategy_preference, selectedStrategy.getStrategyProvider().getStrategyName());
        DiagramType diagrams = (DiagramType) diagramTypeCombo.getSelectedItem();
        prefs.put(InferenceRules.diagram_type_preference, diagrams.name());
        Boolean backgroundSearch = backgroundSearchCheckbox.isSelected();
        prefs.put(AutomaticProverThread.background_preference, backgroundSearch.toString());
        Boolean showLowLevel = levelCheckbox.isSelected();
        prefs.put(Tactics.level_preference, showLowLevel.toString());
        dispose();
    }

    private ComboBoxModel<ProverListItem> getProverComboList() {
        Set<String> provers = AutomaticProvers.getKnownAutomaticProvers();
        ProverListItem[] proverItems = new ProverListItem[provers.size()];
        int i = 0;
        for (String providerName : provers) {
            proverItems[i++] = new ProverListItem(AutomaticProvers.getProvider(providerName));
        }
        Arrays.sort(proverItems);
        ComboBoxModel<ProverListItem> model = new DefaultComboBoxModel<>(proverItems);
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

    private ComboBoxModel<StrategyListItem> getStrategyComboList() {
        Set<String> strategies = Strategies.getKnownStrategies();
        StrategyListItem[] stragetyItems = new StrategyListItem[strategies.size()];
        int i = 0;
        for (String strategyName : strategies) {
            stragetyItems[i++] = new StrategyListItem(Strategies.getProvider(strategyName));
        }
        Arrays.sort(stragetyItems);
        ComboBoxModel<StrategyListItem> model = new DefaultComboBoxModel<>(stragetyItems);
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

    private Boolean getBackGroundSearchEnabled() {
        Preferences prefs = Preferences.userNodeForPackage(SettingsDialog.class);
        String selected = prefs.get(AutomaticProverThread.background_preference, null);
        if (selected != null) {
            return Boolean.valueOf(selected);
        }
        return Boolean.FALSE;

    }

    private Boolean getShowLowLevelTactics() {
        Preferences prefs = Preferences.userNodeForPackage(SettingsDialog.class);
        String selected = prefs.get(Tactics.level_preference, null);
        if (selected != null) {
            return Boolean.valueOf(selected);
        }
        return Boolean.FALSE;
    }

    public Boolean isBackGroundSearchEnabled() {
        return backgroundSearchCheckbox.isSelected();
    }

    public Boolean isShowLowLevelTacticsEnabled() {
        return levelCheckbox.isSelected();
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
