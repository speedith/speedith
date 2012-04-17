/*
 * File name: HyperblocksTopComponent.java
 *    Author: matej
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
package diabelli.hyperblocks.ui;

import java.awt.*;
import openproof.awt.SmartEditMenu;
import openproof.situation.editor.BlocksSitExternalEditor;
import openproof.situation.editor.BlocksSitToolbar;
import openproof.situation.editor.BlocksSitUIController;
import openproof.situation.representation.*;
import openproof.tarski.world.WorldController;
import org.netbeans.api.settings.ConvertAsProperties;
import org.openide.awt.ActionID;
import org.openide.awt.ActionReference;
import org.openide.util.NbBundle.Messages;
import org.openide.windows.TopComponent;

/**
 * Top component which displays something.
 */
@ConvertAsProperties(dtd = "-//diabelli.hyperblocks.ui//Hyperblocks//EN",
autostore = false)
@TopComponent.Description(preferredID = "HyperblocksTopComponent",
//iconBase="SET/PATH/TO/ICON/HERE", 
persistenceType = TopComponent.PERSISTENCE_ALWAYS)
@TopComponent.Registration(mode = "editor", openAtStartup = true)
@ActionID(category = "Window", id = "diabelli.hyperblocks.ui.HyperblocksTopComponent")
@ActionReference(path = "Menu/Window" /*
 * , position = 333
 */)
@TopComponent.OpenActionRegistration(displayName = "#CTL_HyperblocksAction",
preferredID = "HyperblocksTopComponent")
@Messages({
    "CTL_HyperblocksAction=Hyperblocks",
    "CTL_HyperblocksTopComponent=Hyperblocks Window",
    "HINT_HyperblocksTopComponent=This is a Hyperblocks window"
})
public final class HyperblocksTopComponent extends TopComponent {

    public HyperblocksTopComponent() {
        initComponents();
        setName(Bundle.CTL_HyperblocksTopComponent());
        setToolTipText(Bundle.HINT_HyperblocksTopComponent());
//        // Print out the 'java.libs.path'
//        String property = System.getProperty("java.libs.path");
//        System.out.println(property);
//        property = System.getProperty("java.library.path");
//        System.out.println(property);


        BlocksSitExternalEditor bsee = new BlocksSitExternalEditor();
        bsee.init(new BorderLayout());
        ExtendedSituation mySituation = new ExtendedSituation();
        bsee.setSituation(mySituation);
        BlocksSitUIController controller = bsee.createNewController();

        MenuBar menu = new MenuBar();

        Menu blocks = new Menu("Blocks");
        MenuItem newBlock = new MenuItem("New block");
        newBlock.setActionCommand(WorldController.NEW_BLOCK_CMD);
        blocks.add(newBlock);
        MenuItem delBlock = new MenuItem("Delete block");
        delBlock.setActionCommand(SmartEditMenu.CLEAR_CMD);
        blocks.add(delBlock);
        MenuItem toggle = new MenuItem("Toggle");
        toggle.setActionCommand(WorldController.TOGGLE_2D_CMD);
        blocks.add(toggle);

        menu.add(blocks);
//        setMenuBar(menu);

        controller.setNewBlockMI(newBlock);
        controller.setDelBlockMI(delBlock);
        controller.setToggle2DMI(toggle);

        jPanel1.add(bsee, BorderLayout.CENTER);
        BlocksSitToolbar toolbar = controller.getToolbar();
        toolbar.setEnabled(true);
        toolbar.setEditing(true);

        controller.enableNewBlockItem(true);
        controller.enableDelBlockItem(true);

        jPanel1.add(toolbar, BorderLayout.SOUTH);

        // Building up a situation
        HyperBlock block = new HyperBlock();
        mySituation.applyChange(new NewBlockChangeDelta(block));
        mySituation.applyChange(new SizeChangeDelta(block, HyperBlock.LARGE));
        mySituation.applyChange(new AddLabelChangeDelta(block, "a"));
        mySituation.applyChange(new ShapeChangeDelta(block, HyperBlock.CUBE));
        mySituation.applyChange(new MoodChangeDelta(block, HyperBlock.HAPPY));
        mySituation.applyChange(new PositionChangeDelta(block, new Point(2, 6), null));

        // Building up a situation
        HyperBlock blockB = new HyperBlock();
        mySituation.applyChange(new NewBlockChangeDelta(blockB));
        mySituation.applyChange(new SizeChangeDelta(blockB, HyperBlock.SMALL));
        mySituation.applyChange(new AddLabelChangeDelta(blockB, "b"));
        mySituation.applyChange(new ShapeChangeDelta(blockB, HyperBlock.TET));
        mySituation.applyChange(new MoodChangeDelta(blockB, HyperBlock.SAD));
        mySituation.applyChange(new PositionChangeDelta(blockB, new Point(3, 4), null));

        bsee.refresh();

        // This is how you get the representation that is flattened.
        Situation situation = Situation.representedSituation(mySituation);
        //		ObserveRule or = new ObserveRule();
        //		// This is how you observe.
        ////		or.check(mySituation, "some formula");
        //
        //		// This is how you apply
        //		ApplyRule ar = new ApplyRule();
        //		ExtendedSituation es = new ExtendedSituation(mySituation);
        //		// Apply a change to the es...
        //		// ...
        //		// This will check whether the changes (deltas) made from the parent on
        //		// are okay (given the preconditions):
        ////		ar.check(es, new ArrayList(Arrays.asList((OPFormula)null)), null);
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jButton1 = new javax.swing.JButton();
        jPanel1 = new javax.swing.JPanel();

        org.openide.awt.Mnemonics.setLocalizedText(jButton1, org.openide.util.NbBundle.getBundle(HyperblocksTopComponent.class).getString("HyperblocksTopComponent.jButton1.text")); // NOI18N
        jButton1.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jButton1ActionPerformed(evt);
            }
        });

        jPanel1.setLayout(new java.awt.BorderLayout());

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(jPanel1, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addGroup(layout.createSequentialGroup()
                        .addComponent(jButton1)
                        .addGap(0, 214, Short.MAX_VALUE)))
                .addContainerGap())
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jButton1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jPanel1, javax.swing.GroupLayout.DEFAULT_SIZE, 245, Short.MAX_VALUE)
                .addContainerGap())
        );
    }// </editor-fold>//GEN-END:initComponents

    private void jButton1ActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jButton1ActionPerformed
        HyperblocksTestFrame hyperblocksTestFrame = new HyperblocksTestFrame();
        hyperblocksTestFrame.pack();
        hyperblocksTestFrame.setVisible(true);
    }//GEN-LAST:event_jButton1ActionPerformed
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton jButton1;
    private javax.swing.JPanel jPanel1;
    // End of variables declaration//GEN-END:variables

    @Override
    public void componentOpened() {
        // TODO add custom code on component opening
    }

    @Override
    public void componentClosed() {
        // TODO add custom code on component closing
    }

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
}
