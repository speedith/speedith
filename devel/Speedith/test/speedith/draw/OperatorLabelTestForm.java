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

        compoundSpiderDiagramPanel2 = new speedith.ui.SpiderDiagramPanel();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        compoundSpiderDiagramPanel2.setBorder(new javax.swing.border.LineBorder(new java.awt.Color(0, 0, 0), 1, true));
        try {
            compoundSpiderDiagramPanel2.setDiagramString("BinarySD {\n\toperator = \"op -->\",\n\targ1 = BinarySD {\n\t\toperator = \"op &\",\n\t\targ1 = PrimarySD {spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\"], [\"B\", \"C\"]), ([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], [])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])], sh_zones = [([\"B\"], [\"A\", \"C\"])]},\n\t\targ2 = NullSD {}\n\t},\n\targ2 = PrimarySD {spiders = [\"s1\", \"s2\", \"s3\"], habitats = [(\"s1\", [([\"A\"], [\"B\", \"C\"]), ([\"A\", \"B\"], [\"C\"]), ([\"A\", \"B\", \"C\"], [])]), (\"s2\", [([\"B\"], [\"A\", \"C\"])]), (\"s3\", [([\"B\"], [\"A\", \"C\"])])], sh_zones = [([\"B\"], [\"A\", \"C\"])]}\n}");
        } catch (speedith.core.lang.reader.ReadingException e1) {
            e1.printStackTrace();
        }

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(compoundSpiderDiagramPanel2, javax.swing.GroupLayout.DEFAULT_SIZE, 796, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(compoundSpiderDiagramPanel2, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 453, Short.MAX_VALUE)
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
    private speedith.ui.SpiderDiagramPanel compoundSpiderDiagramPanel2;
    // End of variables declaration//GEN-END:variables
}
