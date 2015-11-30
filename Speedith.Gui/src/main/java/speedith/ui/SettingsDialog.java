package speedith.ui;

import speedith.core.reasoning.automatic.AutomaticProver;
import speedith.core.reasoning.automatic.AutomaticProverProvider;
import speedith.core.reasoning.automatic.AutomaticProvers;

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
        //TODO: add provider for strategies and loading of strategies
        String[] strategies = {"None"};
        strategyCombo = new JComboBox(strategies);

        autoProverPanel.setLayout(new GridBagLayout());
        autoProverPanel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));


        GridBagConstraints c = new GridBagConstraints();

        c.gridx = 0;
        c.gridy = 0;
        c.ipadx = 5;
        c.ipady = 5;
        c.anchor = GridBagConstraints.LINE_START;
        typeLabel.setText("Type");
        autoProverPanel.add(typeLabel, c);


        c.gridx = 2;
        c.gridy = 0;
        c.ipadx = 5;
        c.ipady = 5;
        c.anchor = GridBagConstraints.LINE_END;
        autoProverPanel.add(typeCombo,c);



        c.gridx = 0;
        c.gridy = 1;
        c.ipadx = 5;
        c.ipady = 5;
        c.fill = GridBagConstraints.NONE;
        c.anchor = GridBagConstraints.LINE_START;
        strategyLabel.setText("Strategy");
        autoProverPanel.add(strategyLabel, c);



        c.gridx = 2;
        c.gridy = 1;
        c.ipadx = 5;
        c.ipady = 5;
        c.anchor = GridBagConstraints.LINE_END;
        autoProverPanel.add(strategyCombo, c);

        settingsTab.addTab("Auto Prover", autoProverPanel);

        settingsPanel.setLayout(new GridBagLayout());
        c.anchor = GridBagConstraints.CENTER;
        c = new GridBagConstraints();
        c.gridy = 0;
        c.gridx = 0;
        c.fill = GridBagConstraints.BOTH;
        settingsPanel.add(settingsTab, c);

        okButton.setText("Ok");
        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                okbuttonClicked(actionEvent);
            }
        });
        c.gridy = 1;
        c.gridx = 0;
        c.anchor = GridBagConstraints.LINE_START;
        c.fill = GridBagConstraints.NONE;
        settingsPanel.add(okButton, c);


        GridBagLayout layout = new GridBagLayout();
        getContentPane().setLayout(new BorderLayout());
        c.fill = GridBagConstraints.BOTH;
        c.anchor =GridBagConstraints.LINE_START;
        getContentPane().add(settingsPanel, BorderLayout.CENTER);

        pack();
    }

    private void okbuttonClicked(ActionEvent actionEvent) {
        Preferences prefs =  Preferences.userNodeForPackage(SettingsDialog.class);
        ProverListItem selectedProver = (ProverListItem) typeCombo.getSelectedItem();
        prefs.put(AutomaticProvers.prover_preference, selectedProver.getAutomaticProverProvider().getAutomaticProverName() );
        // TODO: add saving of selected strategy
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
}
