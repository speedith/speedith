/*
 * File name: HyperblocksTestFrame.java
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
package diabelli.hyperblocks.ui;

import java.awt.*;
import openproof.awt.SmartEditMenu;
import openproof.situation.editor.BlocksSitExternalEditor;
import openproof.situation.editor.BlocksSitToolbar;
import openproof.situation.editor.BlocksSitUIController;
import openproof.situation.representation.*;
import openproof.tarski.world.WorldController;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class HyperblocksTestFrame extends javax.swing.JFrame {

    /**
     * Creates new form HyperblocksTestFrame
     */
    public HyperblocksTestFrame() {
        String property = System.getProperty("java.library.path");
        System.out.println(property);
        initComponents();


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
        setMenuBar(menu);

        controller.setNewBlockMI(newBlock);
        controller.setDelBlockMI(delBlock);
        controller.setToggle2DMI(toggle);

        getContentPane().add(bsee, BorderLayout.CENTER);
        BlocksSitToolbar toolbar = controller.getToolbar();
        toolbar.setEnabled(true);
        toolbar.setEditing(true);

        controller.enableNewBlockItem(true);
        controller.enableDelBlockItem(true);

        getContentPane().add(toolbar, BorderLayout.SOUTH);

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
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);

        pack();
    }// </editor-fold>//GEN-END:initComponents

    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /*
         * Set the Nimbus look and feel
         */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
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
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(HyperblocksTestFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(HyperblocksTestFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(HyperblocksTestFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(HyperblocksTestFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /*
         * Create and display the form
         */
        java.awt.EventQueue.invokeLater(new Runnable() {

            public void run() {
                new HyperblocksTestFrame().setVisible(true);
            }
        });
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    // End of variables declaration//GEN-END:variables
}
