/*
 *   Project: Speedith
 * 
 * File name: SpeedithMainForm.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
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

/*
 * SpeedithMainForm.java
 *
 * Created on 07-Nov-2011, 10:47:11
 */
package speedith.ui;

import scala.Function1;
import scala.collection.Seq;
import speedith.core.lang.*;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.rules.AddFeet;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.core.reasoning.rules.util.ReasoningUtils;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.core.reasoning.tactical.euler.BasicTacticals;
import speedith.core.reasoning.tactical.euler.SimpleTacticals;
import speedith.core.reasoning.tactical.euler.SingleRuleTacticals;
import speedith.core.reasoning.tactical.euler.Tactics;
import speedith.ui.input.TextSDInputDialog;
import speedith.ui.rules.InteractiveRuleApplication;
import spiderdrawer.ui.MainForm;

import javax.imageio.ImageIO;
import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

import static speedith.i18n.Translations.i18n;

/**
 * The main application window of Speedith.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpeedithMainForm extends javax.swing.JFrame {

  private static final String[] SpeedithIcons = {
    "SpeedithIconVennDiagram-16.png",
    "SpeedithIconVennDiagram-32.png",
    "SpeedithIconVennDiagram-48.png",
    "SpeedithIconVennDiagram-64.png",
    "SpeedithIconVennDiagram-128.png"
  };

  private JMenuItem goalSpiderDrawerInputMenuItem;
  private javax.swing.JMenu drawMenu;
  private javax.swing.JMenuItem openMenuItem;
  private javax.swing.JMenuItem saveMenuItem;
  private javax.swing.JMenuItem exitMenuItem;
  private javax.swing.JMenuItem settingsMenuItem;
  private javax.swing.JMenu fileMenu;
  private javax.swing.JMenuItem useSdExample1MenuItem;
  private javax.swing.JMenuItem useSdExample2MenuItem;
  private javax.swing.JMenuItem useSdExample3MenuItem;
  private javax.swing.JLabel lblAppliedRules;
  private javax.swing.JList lstAppliedRules;
  private javax.swing.JMenuBar menuBar;
  private javax.swing.JMenuItem goalTextInputMenuItem;
  private javax.swing.JPanel pnlRulesSidePane;
  private speedith.ui.ProofPanel proofPanel1;
  private javax.swing.JMenu proofMenu;
  private javax.swing.JMenuItem cropProof;
  private javax.swing.JScrollPane scrlPnlAppliedRules;
  private javax.swing.JMenu reasoningMenu;
  private javax.swing.JMenuItem proveAny;
  private javax.swing.JMenuItem proveFromHere;
  private javax.swing.JFileChooser fileChooser;
  private javax.swing.JMenu tacticsMenu;
  private javax.swing.JMenuItem vennify;
  private javax.swing.JMenuItem devennify;

  /**
   * Creates new form SpeedithMainForm
   */
  public SpeedithMainForm() {
    initComponents();
    try {
      ArrayList<Image> icons = new ArrayList<Image>();
      // Set the icon of this window:
      for (String path : SpeedithIcons) {
        InputStream imgStream = this.getClass().getResourceAsStream(path);
        icons.add(ImageIO.read(imgStream));
      }
      setIconImages(icons);
    } catch (IOException ex) {
      Logger.getLogger(SpeedithMainForm.class.getName()).log(Level.WARNING, "Speedith's icons could not have been loaded.", ex);
    }
  }

  @SuppressWarnings("unchecked")
  private void initComponents() {
    java.awt.GridBagConstraints gridBagConstraints;

    javax.swing.JSplitPane mainSplitPane = new javax.swing.JSplitPane();
    proofPanel1 = new speedith.ui.ProofPanel();
    pnlRulesSidePane = new javax.swing.JPanel();
    lblAppliedRules = new javax.swing.JLabel();
    scrlPnlAppliedRules = new javax.swing.JScrollPane();
    lstAppliedRules = new javax.swing.JList();
    menuBar = new javax.swing.JMenuBar();
    fileMenu = new javax.swing.JMenu();
    settingsMenuItem = new javax.swing.JMenuItem();
    exitMenuItem = new javax.swing.JMenuItem();
    openMenuItem = new javax.swing.JMenuItem();
    saveMenuItem = new javax.swing.JMenuItem();
    drawMenu = new javax.swing.JMenu();
    goalSpiderDrawerInputMenuItem = new javax.swing.JMenuItem();
    goalTextInputMenuItem = new javax.swing.JMenuItem();
    useSdExample1MenuItem = new javax.swing.JMenuItem();
    useSdExample2MenuItem = new javax.swing.JMenuItem();
    useSdExample3MenuItem = new javax.swing.JMenuItem();
    proofMenu = new javax.swing.JMenu();
    cropProof = new javax.swing.JMenuItem();
    reasoningMenu = new javax.swing.JMenu();
    proveAny = new javax.swing.JMenuItem();
    proveFromHere = new javax.swing.JMenuItem();
    tacticsMenu = new javax.swing.JMenu();
    vennify = new javax.swing.JMenuItem();
    devennify = new javax.swing.JMenuItem();

    setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
    setTitle("Speedith");

    proofPanel1.setMinimumSize(new java.awt.Dimension(500, 300));
    proofPanel1.setPreferredSize(new java.awt.Dimension(750, 300));
    mainSplitPane.setLeftComponent(proofPanel1);

    pnlRulesSidePane.setMinimumSize(new java.awt.Dimension(100, 300));
    pnlRulesSidePane.setPreferredSize(new java.awt.Dimension(100, 300));
    pnlRulesSidePane.setLayout(new java.awt.GridBagLayout());

    lblAppliedRules.setLabelFor(lstAppliedRules);
    lblAppliedRules.setText(i18n("MAIN_FORM_RULE_LIST")); // NOI18N
    gridBagConstraints = new java.awt.GridBagConstraints();
    gridBagConstraints.gridx = 0;
    gridBagConstraints.gridy = 0;
    gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
    gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
    gridBagConstraints.weightx = 1.0;
    gridBagConstraints.insets = new java.awt.Insets(0, 3, 0, 0);
    pnlRulesSidePane.add(lblAppliedRules, gridBagConstraints);

    lstAppliedRules.setModel(getRulesList());
    lstAppliedRules.addMouseListener(new java.awt.event.MouseAdapter() {
      public void mouseClicked(java.awt.event.MouseEvent evt) {
        onRuleItemClicked(evt);
      }
    });
    scrlPnlAppliedRules.setViewportView(lstAppliedRules);

    gridBagConstraints = new java.awt.GridBagConstraints();
    gridBagConstraints.gridx = 0;
    gridBagConstraints.gridy = 1;
    gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
    gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
    gridBagConstraints.weightx = 1.0;
    gridBagConstraints.weighty = 1.0;
    gridBagConstraints.insets = new java.awt.Insets(6, 0, 0, 0);
    pnlRulesSidePane.add(scrlPnlAppliedRules, gridBagConstraints);

    mainSplitPane.setRightComponent(pnlRulesSidePane);

    fileMenu.setMnemonic('F');
    fileMenu.setText("File");

    openMenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(KeyEvent.VK_O, java.awt.event.InputEvent.CTRL_MASK));
    openMenuItem.setMnemonic('O');
    openMenuItem.setText("Open Goal");
    openMenuItem.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onOpen(evt);
      }
    });
    fileMenu.add(openMenuItem);

    saveMenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(KeyEvent.VK_S, java.awt.event.InputEvent.CTRL_MASK));
    saveMenuItem.setMnemonic('S');
    saveMenuItem.setText("Save selected Subgoal");
    saveMenuItem.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onSave(evt);
      }
    });
    fileMenu.add(saveMenuItem);

    settingsMenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(KeyEvent.VK_P, java.awt.event.InputEvent.CTRL_MASK));
    settingsMenuItem.setMnemonic('P');
    settingsMenuItem.setText("Preferences");
    settingsMenuItem.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onSettings(evt);
      }
    });
    fileMenu.add(settingsMenuItem);

    exitMenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_Q, java.awt.event.InputEvent.CTRL_MASK));
    exitMenuItem.setMnemonic('x');
    exitMenuItem.setText("Exit");
    exitMenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        exitMenuItemActionPerformed(evt);
      }
    });
    fileMenu.add(exitMenuItem);

    menuBar.add(fileMenu);

    drawMenu.setMnemonic('D');
    drawMenu.setText("Draw");

    goalSpiderDrawerInputMenuItem.setText("Use SpiderDrawer"); // NOI18N
    goalSpiderDrawerInputMenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        onSpiderDrawerClicked(evt);
      }
    });
    drawMenu.add(goalSpiderDrawerInputMenuItem);

    goalTextInputMenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_T, java.awt.event.InputEvent.CTRL_MASK));
    goalTextInputMenuItem.setMnemonic(java.util.ResourceBundle.getBundle("speedith/i18n/strings").getString("MAIN_FORM_TEXT_INPUT_MNEMONIC").charAt(0));
    java.util.ResourceBundle bundle = java.util.ResourceBundle.getBundle("speedith/i18n/strings"); // NOI18N
    goalTextInputMenuItem.setText(bundle.getString("MAIN_FORM_TEXT_INPUT")); // NOI18N
    goalTextInputMenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        onTextInputClicked(evt);
      }
    });
    drawMenu.add(goalTextInputMenuItem);

    useSdExample1MenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_1, java.awt.event.InputEvent.CTRL_MASK));
    useSdExample1MenuItem.setMnemonic(i18n("MAIN_FORM_USE_EXAMPLE1_MNEMONIC").charAt(0));
    useSdExample1MenuItem.setText(i18n("MAIN_FORM_USE_EXAMPLE1")); // NOI18N
    useSdExample1MenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        onExample1(evt);
      }
    });
    drawMenu.add(useSdExample1MenuItem);

    useSdExample2MenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_2, java.awt.event.InputEvent.CTRL_MASK));
    useSdExample2MenuItem.setMnemonic(i18n("MAIN_FORM_USE_EXAMPLE2_MNEMONIC").charAt(0));
    useSdExample2MenuItem.setText(i18n("MAIN_FORM_USE_EXAMPLE2")); // NOI18N
    useSdExample2MenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        onExample2(evt);
      }
    });
    drawMenu.add(useSdExample2MenuItem);

    useSdExample3MenuItem.setAccelerator(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_3, java.awt.event.InputEvent.CTRL_MASK));
    useSdExample3MenuItem.setMnemonic(i18n("MAIN_FORM_USE_EXAMPLE3_MNEMONIC").charAt(0));
    useSdExample3MenuItem.setText(i18n("MAIN_FORM_USE_EXAMPLE3")); // NOI18N
    useSdExample3MenuItem.addActionListener(new java.awt.event.ActionListener() {
      public void actionPerformed(java.awt.event.ActionEvent evt) {
        onExample3(evt);
      }
    });
    drawMenu.add(useSdExample3MenuItem);

    menuBar.add(drawMenu);

    proofMenu.setMnemonic('P');
    proofMenu.setText("Proof");

    cropProof.setText("Reduce Proof to selected Subgoal");
    cropProof.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onCropProof(evt);
      }
    });
    proofMenu.add(cropProof);
    menuBar.add(proofMenu);

    reasoningMenu.setMnemonic('A');
    reasoningMenu.setText("Auto");

    proveAny.setText("Prove");
    proveAny.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onProveAny(evt);
      }
    });
    reasoningMenu.add(proveAny);

    proveFromHere.setText("Prove from the current state");
    proveFromHere.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent evt) {
        onProveFromHere(evt);
      }
    });
    reasoningMenu.add(proveFromHere);
    menuBar.add(reasoningMenu);

    tacticsMenu.setText("Tactics");
    JMenu tacticSubmenu = new javax.swing.JMenu();
    tacticSubmenu.setText("Apply rule tactic");
    for (final Method tactic:  SingleRuleTacticals.class.getDeclaredMethods()) {
      JMenuItem tacticButton = new javax.swing.JMenuItem();
      tacticButton.setText(tactic.getName());
      tacticButton.addActionListener(new ActionListener() {
        @Override
        public void actionPerformed(ActionEvent evt) {
          applyTactic(tactic);
        }
      });
      tacticSubmenu.add(tacticButton);
      tacticsMenu.add(tacticSubmenu);

    }


    for (final Method tactical:  SimpleTacticals.class.getDeclaredMethods()) {
      JMenuItem tacticalButton = new javax.swing.JMenuItem();
      tacticalButton.setText(tactical.getName());
      tacticalButton.addActionListener(new ActionListener() {
        @Override
        public void actionPerformed(ActionEvent evt) {
          applyTactical(tactical);
        }
      });
      tacticsMenu.add(tacticalButton);
      menuBar.add(tacticsMenu);

    }

    setJMenuBar(menuBar);

    javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
    getContentPane().setLayout(layout);
    layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(mainSplitPane, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 995, Short.MAX_VALUE)
    );
    layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(mainSplitPane, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 406, Short.MAX_VALUE)
    );


    fileChooser = new JFileChooser();

    pack();
  }// </editor-fold>//GEN-END:initComponents

  private void applyTactic(Method tactic) {
    if (!proofPanel1.isFinished()) {
      Proof intermediate = new ProofTrace(proofPanel1);
      Proof result = null;
      try {
        result = (Proof) tactic.invoke(SingleRuleTacticals.class, intermediate);
      } catch (IllegalAccessException e) {
        e.printStackTrace();
      } catch (InvocationTargetException e) {
        if (e.getCause() instanceof TacticApplicationException) {
          TacticApplicationException tacticE = (TacticApplicationException) e.getCause();
          JOptionPane.showMessageDialog(this, tacticE.getMessage());
        }
      }
      proofPanel1.replaceCurrentProof(result);
    } else {
      JOptionPane.showMessageDialog(this, "No subgoals are open");
    }
  }




  private void applyTactical(Method tactical) {
    if (!proofPanel1.isFinished()) {
      Proof intermediate = new ProofTrace(proofPanel1);
      Seq<Proof> result = null;
      try {
        result = (Seq<Proof>) tactical.invoke(SimpleTacticals.class, intermediate);
      } catch (IllegalAccessException e) {
        e.printStackTrace();
      } catch (InvocationTargetException e) {
        e.printStackTrace();
      }
      if (result !=null && result.nonEmpty()) {
        proofPanel1.replaceCurrentProof(result.head());
      } else {
        System.out.println(result);
        JOptionPane.showMessageDialog(this, "Tactic could not be applied");
      }
    } else {
      JOptionPane.showMessageDialog(this, "No subgoals are open");
    }
  }

  private void onCropProof(ActionEvent evt) {
    if (proofPanel1.getSelected() != null) {
      proofPanel1.reduceToSelected();
    }
  }


  private void onOpen(ActionEvent evt) {
    int returnVal = fileChooser.showOpenDialog(this);
    if (returnVal == JFileChooser.APPROVE_OPTION) {
      File file = fileChooser.getSelectedFile();
      try {
        SpiderDiagram input = SpiderDiagramsReader.readSpiderDiagram(file);
        proofPanel1.newProof(Goals.createGoalsFrom(ReasoningUtils.normalize(input)));
      } catch (IOException ioe) {
        JOptionPane.showMessageDialog(this, "An error occurred while accessing the file:\n" + ioe.getLocalizedMessage());
      } catch (ReadingException re) {
        JOptionPane.showMessageDialog(this, "An error occurred while reading the contents of the file:\n" + re.getLocalizedMessage());
      }
      this.setTitle("Speedith"+": " + file.getName());
    }
  }

  private void onSave(ActionEvent evt) {
    if (proofPanel1.getGoals().isEmpty()) {
      JOptionPane.showMessageDialog(this, "No subgoal to be saved exists.");
      return;
    }
    if (proofPanel1.getSelected() != null) {
        SpiderDiagram toSave = proofPanel1.getSelected();
        int returnVal = fileChooser.showSaveDialog(this);
        if (returnVal == JFileChooser.APPROVE_OPTION) {
          File file = fileChooser.getSelectedFile();
          if (file.exists()) {
            int reallySave = JOptionPane.showConfirmDialog(this, "File " + file.getName() + " exists at given path. Save anyway?", "File already exists", JOptionPane.YES_NO_OPTION);
            if (reallySave == JOptionPane.NO_OPTION) {
              return;
            }
          }
          try {

            FileWriter writer = new FileWriter(file);
            writer.write(toSave.toString());
            writer.flush();
            writer.close();
          } catch (IOException ioe) {
            JOptionPane.showMessageDialog(this, "An error occurred while accessing the file:\n" + ioe.getLocalizedMessage());
          }
        }

      } else {
        JOptionPane.showMessageDialog(this, "No subgoal selected", "No subgoal selected", JOptionPane.ERROR_MESSAGE);
      }


  }
  private void onSettings(ActionEvent evt) {
    SettingsDialog settings = new SettingsDialog(this, true);
    settings.setVisible(true);
    proofPanel1.setProver(settings.getSelectedProver());
    proofPanel1.getProver().setStrategy(settings.getSelectedStrategy());
  }

  private void onProveAny(ActionEvent evt) {
    Goals initial =  proofPanel1.getInitialGoals();
    try {
       proofPanel1.generateProof(initial);
    } catch (AutomaticProofException e) {
      JOptionPane.showMessageDialog(this, e.getLocalizedMessage());
    }
  }

  private void onProveFromHere(ActionEvent evt) {
    try {
      proofPanel1.extendProof(proofPanel1);
    } catch (AutomaticProofException e) {
      JOptionPane.showMessageDialog(this, e.getLocalizedMessage());
    }
  }

  private void onSpiderDrawerClicked(ActionEvent evt) {
    MainForm spiderDrawer = new MainForm(this, true, false);
    boolean done = spiderDrawer.showDialog();

    if (done) {
      SpiderDiagram spiderDiagram;
      try {
        spiderDiagram = SpiderDiagramsReader.readSpiderDiagram(spiderDrawer.getSpiderDiagram());
        proofPanel1.newProof(Goals.createGoalsFrom(spiderDiagram));
      } catch (Exception ex) {
        System.out.println(ex.getMessage());
      }
    }
  }

  private void exitMenuItemActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_exitMenuItemActionPerformed
    this.dispose();
  }//GEN-LAST:event_exitMenuItemActionPerformed

  private void onExample1(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_onExample1
    proofPanel1.newProof(Goals.createGoalsFrom(getExampleA()));
    setTitle("Speedith" + ": " + "Example 1");
  }//GEN-LAST:event_onExample1

  private void onExample2(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_onExample2
    proofPanel1.newProof(Goals.createGoalsFrom(getExampleB()));
    setTitle("Speedith"+": "+"Example 2");
  }//GEN-LAST:event_onExample2

  private void onExample3(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_onExample3
    proofPanel1.newProof(Goals.createGoalsFrom(getExampleC()));
    setTitle("Speedith"+": "+"Example 3");
  }//GEN-LAST:event_onExample3

  private void onRuleItemClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_onRuleItemClicked
    if (evt.getClickCount() == 2) {
      if (!proofPanel1.isFinished()) {
        int index = lstAppliedRules.locationToIndex(evt.getPoint());
        DefaultComboBoxModel model = (DefaultComboBoxModel) lstAppliedRules.getModel();
        InfRuleListItem selectedRule = (InfRuleListItem) model.getElementAt(index);
        applyRule(selectedRule);
      }
    }
  }//GEN-LAST:event_onRuleItemClicked

  private void onTextInputClicked(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_onTextInputClicked
    TextSDInputDialog dialog = new TextSDInputDialog(this, true);
    if (proofPanel1.getLastGoals() != null && !proofPanel1.getLastGoals().isEmpty()) {
      dialog.setSpiderDiagramText(proofPanel1.getLastGoals().getGoalAt(0));
    } else {
      dialog.setSpiderDiagramText(getExampleA());
    }
    dialog.setVisible(true);
    if (!dialog.isCancelled() && dialog.getSpiderDiagram() != null) {
      proofPanel1.newProof(Goals.createGoalsFrom(ReasoningUtils.normalize(dialog.getSpiderDiagram())));
      setTitle("Speedith");
    }
  }//GEN-LAST:event_onTextInputClicked

  /**
   * @param args the command line arguments
   */
  public static void main(String args[]) {
        /*
         * Set the Nimbus look and feel
         */
        /*
         * If Nimbus (introduced in Java SE 6) is not available, stay with the
         * default look and feel. For details see
         * http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html
         */
    try {
      for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
        if ("Nimbus".equals(info.getName())) {
          javax.swing.UIManager.setLookAndFeel(info.getClassName());
          break;
        }
      }
    } catch (ClassNotFoundException | InstantiationException | IllegalAccessException | UnsupportedLookAndFeelException ex) {
      java.util.logging.Logger.getLogger(SpeedithMainForm.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
    }

        /*
         * Create and display the form
         */
    java.awt.EventQueue.invokeLater(new Runnable() {
      public void run() {
        new SpeedithMainForm().setVisible(true);
      }
    });
  }

  /**
   * The first main example used in most of our papers. Useful for testing the
   * rules: split spider, add feet, idempotency, and tautology of implication.
   */
  public static CompoundSpiderDiagram getExampleA() {
    PrimarySpiderDiagram psd1 = getSDExample1();
    PrimarySpiderDiagram psd2 = getSDExample7();
    CompoundSpiderDiagram csd = SpiderDiagrams.createCompoundSD(Operator.Implication, psd1, psd2);
    return csd;
  }

  /**
   * The second example. Useful for testing the rule: idempotency.
   */
  public static SpiderDiagram getExampleB() {
    try {
      return SpiderDiagramsReader.readSpiderDiagram("BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op &\" }");
    } catch (Exception ex) {
      throw new RuntimeException();
    }
  }

  /**
   * The third example. Useful for testing the rule: implication tautology.
   */
  public static SpiderDiagram getExampleC() {
    try {
      return SpiderDiagramsReader.readSpiderDiagram("BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op -->\" }");
    } catch (Exception ex) {
      throw new RuntimeException();
    }
  }

  /**
   * s1: A, B s2: AB
   */
  public static PrimarySpiderDiagram getSDExample1() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionA_B__B_A();
    Region s2Region = regionAB();
    emptyPSD = emptyPSD.addSpider("t1", s1Region);
    return emptyPSD.addSpider("t2", s2Region);
  }

  /**
   * s1: A s2: AB
   */
  public static PrimarySpiderDiagram getSDExample5() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionA_B();
    Region s2Region = regionAB();
    emptyPSD = emptyPSD.addSpider("s1", s1Region);
    return emptyPSD.addSpider("s2", s2Region);
  }

  /**
   * s1: B s2: AB
   */
  public static PrimarySpiderDiagram getSDExample6() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionB_A();
    Region s2Region = regionAB();
    emptyPSD = emptyPSD.addSpider("s1", s1Region);
    return emptyPSD.addSpider("s2", s2Region);
  }

  /**
   * s1: A, AB s2: B, AB
   */
  public static PrimarySpiderDiagram getSDExample7() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionA_B__AB();
    Region s2Region = regionB_A__AB();
    emptyPSD = emptyPSD.addSpider("u1", s1Region);
    return emptyPSD.addSpider("u2", s2Region);
  }

  /**
   * s1: B, AB s2: AB
   */
  public static PrimarySpiderDiagram getSDExample8() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionB_A__AB();
    Region s2Region = regionAB();
    emptyPSD = emptyPSD.addSpider("s1", s1Region);
    return emptyPSD.addSpider("s2", s2Region);
  }

  /**
   * s1: B, AB s2: A, AB
   */
  public static PrimarySpiderDiagram getSDExample9() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionB_A__AB();
    Region s2Region = regionA_B__AB();
    emptyPSD = emptyPSD.addSpider("s1", s1Region);
    return emptyPSD.addSpider("s2", s2Region);
  }

  /**
   * s1: A, AB s2: AB
   */
  public static PrimarySpiderDiagram getSDExample10() {
    PrimarySpiderDiagram emptyPSD = SpiderDiagrams.createPrimarySD(null, null, null, null);
    Region s1Region = regionA_B__AB();
    Region s2Region = regionAB();
    emptyPSD = emptyPSD.addSpider("s1", s1Region);
    return emptyPSD.addSpider("s2", s2Region);
  }

  public static Goals getStep0() {
    CompoundSpiderDiagram csd = getExampleA();
    return Goals.createGoalsFrom(csd);
  }

  public static Goals getStep1() {
    RuleArg ruleArg = new SpiderRegionArg(0, 1, "s1", regionA_B());
    return applyInferenceRule(SplitSpiders.InferenceRuleName, ruleArg, getStep0());
  }

  public static Goals getStep2() {
    RuleArg ruleArg = new SpiderRegionArg(0, 2, "s1", regionAB());
    return applyInferenceRule(AddFeet.InferenceRuleName, ruleArg, getStep1());
  }

  public static Goals getStep3() {
    RuleArg ruleArg = new SpiderRegionArg(0, 3, "s1", regionAB());
    return applyInferenceRule(AddFeet.InferenceRuleName, ruleArg, getStep2());
  }

  public static Goals getStep4() {
    RuleArg ruleArg = new SpiderRegionArg(0, 2, "s2", regionB_A());
    return applyInferenceRule(AddFeet.InferenceRuleName, ruleArg, getStep3());
  }

  public static CompoundSpiderDiagram getSDExample2() {
    PrimarySpiderDiagram psd1 = getSDExample1();
    PrimarySpiderDiagram psd2 = getSDExample1();
    CompoundSpiderDiagram csd = SpiderDiagrams.createCompoundSD(Operator.Equivalence, psd1, psd2);
    return csd;
  }

  public static NullSpiderDiagram getSDExample3() {
    return SpiderDiagrams.createNullSD();
  }

  public static CompoundSpiderDiagram getSDExample4() {
    PrimarySpiderDiagram sd1 = getSDExample1();
    SpiderDiagram sd2 = getSDExample2();
    CompoundSpiderDiagram csd = SpiderDiagrams.createCompoundSD(Operator.Conjunction, sd1, sd2);
    return csd;
  }

  public static CompoundSpiderDiagram getSDExample11() {
    SpiderDiagram sd1 = getSDExample4();
    SpiderDiagram sd2 = SpiderDiagrams.createNullSD();
    CompoundSpiderDiagram csd = SpiderDiagrams.createCompoundSD(Operator.Equivalence, sd1, sd2);
    return csd;
  }

  private ComboBoxModel getRulesComboList() {
    Set<String> knownInferenceRules = InferenceRules.getKnownInferenceRules();
    InfRuleListItem[] infRules = new InfRuleListItem[knownInferenceRules.size()];
    int i = 0;
    for (String providerName : knownInferenceRules) {
      infRules[i++] = new InfRuleListItem(InferenceRules.getProvider(providerName));
    }
    Arrays.sort(infRules);
    return new DefaultComboBoxModel<>(infRules);
  }

  private ListModel<InfRuleListItem> getRulesList() {
    Set<String> knownInferenceRules = InferenceRules.getKnownInferenceRules();
    InfRuleListItem[] infRules = new InfRuleListItem[knownInferenceRules.size()];
    int i = 0;
    for (String providerName : knownInferenceRules) {
      infRules[i++] = new InfRuleListItem(InferenceRules.getProvider(providerName));
    }
    Arrays.sort(infRules);
    return new DefaultComboBoxModel<>(infRules);

  }

  private static class InfRuleListItem implements Comparable<InfRuleListItem> {

    private final InferenceRuleProvider<? extends RuleArg> infRuleProvider;

    public InfRuleListItem(InferenceRuleProvider<? extends RuleArg> infRuleProvider) {
      if (infRuleProvider == null) {
        throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "infRuleProvider"));
      }
      this.infRuleProvider = infRuleProvider;
    }

    public InferenceRuleProvider<? extends RuleArg> getInfRuleProvider() {
      return infRuleProvider;
    }

    @Override
    public String toString() {
      return infRuleProvider.getPrettyName();
    }

    @Override
    public int compareTo(InfRuleListItem o) {
      return infRuleProvider.toString().compareToIgnoreCase(o.toString());
    }
  }

  private static Goals applyInferenceRule(String infRuleName, RuleArg ruleArg, Goals goals0) {
    InferenceRule<? extends RuleArg> infRule = InferenceRules.getInferenceRule(infRuleName);
    try {
      RuleApplicationResult rar = infRule.apply(ruleArg, goals0);
      goals0 = rar.getGoals();
    } catch (RuleApplicationException ex) {
      throw new RuntimeException(ex);
    }
    return goals0;
  }

  private static Region regionA_B() {
    return new Region(zoneA_B());
  }

  private static Region regionA_B__AB() {
    return new Region(zoneA_B(), zoneAB());
  }

  private static Region regionA_B__B_A() {
    return new Region(zoneA_B(), zoneB_A());
  }

  private static Region regionB_A() {
    return new Region(zoneB_A());
  }

  private static Region regionB_A__AB() {
    return new Region(zoneB_A(), zoneAB());
  }

  private static Region regionAB() {
    return new Region(zoneAB());
  }

  private static Zone zoneAB() {
    return Zone.fromInContours("A", "B");
  }

  private static Zone zoneA_B() {
    return Zone.fromInContours("A").withOutContours("B");
  }

  private static Zone zoneB_A() {
    return Zone.fromInContours("B").withOutContours("A");
  }

  private void applyRule(InfRuleListItem selectedRule) {
    int subgoalIndex = 0;
    try {
     boolean test =  InteractiveRuleApplication.applyRuleInteractively(this, selectedRule.getInfRuleProvider().getInferenceRule(), subgoalIndex, proofPanel1);
   //   System.out.println("Cost:"+ proofPanel1.getProver().getStrategy().getCost(proofPanel1)+"\tHeuristic:"+proofPanel1.getProver().getStrategy().getHeuristic(proofPanel1));
    } catch (Exception ex) {
      JOptionPane.showMessageDialog(this, ex.getLocalizedMessage());
    }
  }
}
