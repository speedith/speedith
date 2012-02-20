/*
 *   Project: Speedith
 * 
 * File name: OperatorPanel.java
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
 * OperatorPanel.java
 *
 * Created on 29-Sep-2011, 10:04:27
 */
package speedith.ui;

import speedith.core.i18n.Translations;
import speedith.core.lang.Operator;

/**
 * This label displays the spider-diagrammatic operators.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class OperatorPanel extends javax.swing.JPanel {

    /**
     * Creates an empty operator label.
     * <p>Use {@link OperatorPanel#setOperator(speedith.core.lang.Operator)} to
     * change what this label displays.</p>
     */
    public OperatorPanel() {
        this(null);
    }

    /**
     * Creates a new operator label with the given operator.
     * @param operator the operator to be displayed initially.
     */
    public OperatorPanel(Operator operator) {
        initComponents();
        setOperator(operator);
    }

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        lblOperator = new javax.swing.JLabel();

        setBackground(new java.awt.Color(255, 255, 255));
        setMinimumSize(new java.awt.Dimension(40, 40));
        setPreferredSize(new java.awt.Dimension(40, 40));
        setLayout(new java.awt.BorderLayout());

        lblOperator.setFont(new java.awt.Font("Dialog", 0, 24)); // NOI18N
        lblOperator.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
        add(lblOperator, java.awt.BorderLayout.CENTER);
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel lblOperator;
    // End of variables declaration//GEN-END:variables
    // <editor-fold defaultstate="collapsed" desc="Constants">
    private static final String NegationSign = "¬";
    private static final String DisjunctionSign = "∨";
    private static final String ConjunctionSign = "∧";
    private static final String ImplicationSign = "⟶";
    private static final String EquivalenceSign = "⟷";
    // </editor-fold>
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private Operator operator;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * Returns the currently displayed operator.
     * @return the currently displayed operator.
     */
    public final Operator getOperator() {
        return operator;
    }

    /**
     * Sets the currently displayed operator in this operator label.
     * @param operator the new operator to display in this label.
     */
    public final void setOperator(Operator operator) {
        if (this.operator != operator) {
            this.operator = operator;
            if (this.operator == null) {
                lblOperator.setText("");
            } else {
                switch (this.operator) {
                    case Conjunction:
                        lblOperator.setText(ConjunctionSign);
                        break;
                    case Disjunction:
                        lblOperator.setText(DisjunctionSign);
                        break;
                    case Implication:
                        lblOperator.setText(ImplicationSign);
                        break;
                    case Negation:
                        lblOperator.setText(NegationSign);
                        break;
                    case Equivalence:
                        lblOperator.setText(EquivalenceSign);
                        break;
                    default:
                        throw new RuntimeException(Translations.i18n("GERR_ILLEGAL_STATE"));
                }
            }
        }
    }
    // </editor-fold>
}
