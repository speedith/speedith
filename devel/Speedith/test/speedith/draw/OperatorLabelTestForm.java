/*
 *   Project: Speedith
 * 
 * File name: OperatorLabelTestForm.java
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
 * OperatorLabelTestForm.java
 *
 * Created on 29-Sep-2011, 11:51:27
 */
package speedith.draw;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class OperatorLabelTestForm extends javax.swing.JFrame {

    /** Creates new form OperatorLabelTestForm */
    public OperatorLabelTestForm() {
        initComponents();
    }

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        operatorLabel1 = new speedith.draw.OperatorPanel();
        primarySpiderDiagramPanel1 = new speedith.draw.PrimarySpiderDiagramPanel();
        compoundSpiderDiagramPanel2 = new speedith.draw.CompoundSpiderDiagramPanel();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        operatorLabel1.setOperator(speedith.core.lang.Operator.Equivalence);

        try {
            primarySpiderDiagramPanel1.setDiagramString("PrimarySD {spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\"], [\"B\", \"C\"]), ([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], [])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])], sh_zones = [([\"B\"], [\"A\", \"C\"])]}");
        } catch (speedith.core.lang.reader.ReadingException e1) {
            e1.printStackTrace();
        }
        primarySpiderDiagramPanel1.setPreferredSize(new java.awt.Dimension(200, 200));

        javax.swing.GroupLayout primarySpiderDiagramPanel1Layout = new javax.swing.GroupLayout(primarySpiderDiagramPanel1);
        primarySpiderDiagramPanel1.setLayout(primarySpiderDiagramPanel1Layout);
        primarySpiderDiagramPanel1Layout.setHorizontalGroup(
            primarySpiderDiagramPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGap(0, 200, Short.MAX_VALUE)
        );
        primarySpiderDiagramPanel1Layout.setVerticalGroup(
            primarySpiderDiagramPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGap(0, 200, Short.MAX_VALUE)
        );

        try {
            compoundSpiderDiagramPanel2.setDiagramString("BinarySD { \toperator = \"op -->\", \targ1 = PrimarySD {spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\"], [\"B\", \"C\"]), ([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], [])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])], sh_zones = [([\"B\"], [\"A\", \"C\"])]}, \targ2 = PrimarySD {spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\"], [\"B\", \"C\"]), ([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], [])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])], sh_zones = [([\"B\"], [\"A\", \"C\"])]} }");
        } catch (speedith.core.lang.reader.ReadingException e1) {
            e1.printStackTrace();
        }

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addComponent(primarySpiderDiagramPanel1, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(142, 142, 142)
                .addComponent(operatorLabel1, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addContainerGap(414, Short.MAX_VALUE))
            .addComponent(compoundSpiderDiagramPanel2, javax.swing.GroupLayout.DEFAULT_SIZE, 796, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                    .addComponent(primarySpiderDiagramPanel1, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addGroup(layout.createSequentialGroup()
                        .addGap(80, 80, 80)
                        .addComponent(operatorLabel1, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(compoundSpiderDiagramPanel2, javax.swing.GroupLayout.DEFAULT_SIZE, 247, Short.MAX_VALUE))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
         * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html 
         */
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(OperatorLabelTestForm.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(OperatorLabelTestForm.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(OperatorLabelTestForm.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(OperatorLabelTestForm.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {

            public void run() {
                new OperatorLabelTestForm().setVisible(true);
            }
        });
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private speedith.draw.CompoundSpiderDiagramPanel compoundSpiderDiagramPanel2;
    private speedith.draw.OperatorPanel operatorLabel1;
    private speedith.draw.PrimarySpiderDiagramPanel primarySpiderDiagramPanel1;
    // End of variables declaration//GEN-END:variables
}
