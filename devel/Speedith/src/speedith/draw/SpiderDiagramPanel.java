/*
 *   Project: Speedith
 * 
 * File name: SpiderDiagramPanel.java
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
 * SpiderDiagramPanel.java
 *
 * Created on 29-Sep-2011, 13:46:10
 */
package speedith.draw;

import icircles.util.CannotDrawException;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.util.ArrayList;
import java.util.Iterator;
import javax.swing.JLabel;
import javax.swing.JPanel;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.util.Mapping;
import speedith.core.util.Sequences;
import static speedith.i18n.Translations.i18n;

/**
 * This panel displays all types of {@link SpiderDiagram spider diagrams}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagramPanel extends javax.swing.JPanel {

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new compound spider diagram panel with nothing displayed on it.
     * <p>You can set a diagram to be shown through {@link SpiderDiagramPanel#setDiagram(speedith.core.lang.SpiderDiagram)}.</p>
     */
    public SpiderDiagramPanel() {
        this(null);
    }

    /**
     * Creates a new compound spider diagram panel with the given compound
     * spider diagram.
     *
     * @param diagram the diagram to display in this panel. <p>May be {@code null}
     * in which case nothing will be displayed.</p>
     */
    public SpiderDiagramPanel(SpiderDiagram diagram) {
        initComponents();
        setDiagram(diagram);
    }
    //</editor-fold>

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        diagrams = new javax.swing.JPanel();

        setBorder(javax.swing.BorderFactory.createLineBorder(new java.awt.Color(153, 153, 153)));

        diagrams.setBackground(new java.awt.Color(255, 255, 255));

        javax.swing.GroupLayout diagramsLayout = new javax.swing.GroupLayout(diagrams);
        diagrams.setLayout(diagramsLayout);
        diagramsLayout.setHorizontalGroup(
            diagramsLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGap(0, 330, Short.MAX_VALUE)
        );
        diagramsLayout.setVerticalGroup(
            diagramsLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGap(0, 234, Short.MAX_VALUE)
        );

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(diagrams, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(diagrams, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
        );
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JPanel diagrams;
    // End of variables declaration//GEN-END:variables
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private SpiderDiagram diagram;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the currently presented diagram. <p>May be {@code null}, which
     * indicates that the panel is empty.</p>
     *
     * @return the currently presented diagram, or {@code null} is no diagram is
     * currently being shown.
     */
    public SpiderDiagram getDiagram() {
        return diagram;
    }

    /**
     * Sets the currently shown diagram. <p>May be {@code null}, which indicates
     * that the panel should be empty.</p>
     *
     * @param diagram the new diagram to show, or {@code null} if no diagram is
     * to be shown.
     */
    public final void setDiagram(SpiderDiagram diagram) {
        if (this.diagram != diagram) {
            this.diagram = diagram;
            diagrams.removeAll();
            if (this.diagram != null) {
                try {
                    drawDiagram();
                } catch (Exception ex) {
                    drawErrorLabel();
                }
            } else {
                drawNoDiagramLabel();
            }
            validate();
            repaint();
        }
    }

    /**
     * Returns the string representation of the currently shown diagram.
     *
     * @return the string representation of the currently shown diagram.
     */
    public String getDiagramString() {
        return this.diagram == null ? "" : this.diagram.toString();
    }

    /**
     * Sets the currently shown diagram via its string representation. <p>This
     * method tries to parse the string into a spider diagram and draws it.</p>
     * <p>Here is an example of a valid string:
     * <pre>BinarySD {
     *      operator = "op -->",
     *      arg1 = PrimarySD {spiders = ["s1", "s2", "s3"], habitats = [("s1", [(["A"], ["B", "C"]), (["A", "B"], ["C"]), (["A", "B", "C"], [])]), ("s2", [(["B"], ["A", "C"])]), ("s3", [(["B"], ["A", "C"])])], sh_zones = [(["B"], ["A", "C"])]},
     *      arg2 = PrimarySD {spiders = ["s1", "s2", "s3"], habitats = [("s1", [(["A"], ["B", "C"]), (["A", "B"], ["C"]), (["A", "B", "C"], [])]), ("s2", [(["B"], ["A", "C"])]), ("s3", [(["B"], ["A", "C"])])], sh_zones = [(["B"], ["A", "C"])]}
     * }</pre> </p>
     *
     * @param diagram the string representation of the diagram to present.
     * @throws ReadingException thrown if the string does not represent a valid
     * spider diagram.
     * @throws IllegalArgumentException thrown if the string is a valid spider
     * diagram but not a primary spider diagram.
     */
    public void setDiagramString(String diagram) throws ReadingException {
        if (diagram == null || diagram.isEmpty()) {
            setDiagram(null);
        } else {
            setDiagram(SpiderDiagramsReader.readSpiderDiagram(diagram));
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    /**
     * This method does not remove any components, it just adds an error label
     * saying 'Drawing failed'.
     */
    private void drawErrorLabel() {
        JLabel errorLabel = new JLabel();
        errorLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
        errorLabel.setText(i18n("PSD_LABEL_DISPLAY_ERROR"));
        diagrams.add(errorLabel);
        refreshPrefSize();
    }

    /**
     * This method does not remove any components, it just adds an error label
     * saying 'No diagram'.
     */
    private void drawNoDiagramLabel() {
        JLabel noDiagramLbl = new JLabel();
        noDiagramLbl.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
        noDiagramLbl.setText(i18n("CSD_PANEL_NO_DIAGRAM"));
        diagrams.add(noDiagramLbl);
        refreshPrefSize();
    }

    /**
     * This method puts the diagram panels onto this one. <p>This method does
     * not remove any components, it just adds them to this panel.</p> <p>In
     * case of failure, this method throws an exception and does not put any
     * components onto this panel.</p>
     */
    private void drawDiagram() throws CannotDrawException {
        if (diagram != null) {
            if (diagram instanceof CompoundSpiderDiagram) {
                CompoundSpiderDiagram csd = (CompoundSpiderDiagram) diagram;
                switch (csd.getOperator()) {
                    case Conjunction:
                    case Disjunction:
                    case Equivalence:
                    case Implication:
                        drawInfixDiagram(csd);
                        break;
                    case Negation:
                        drawPrefixDiagram(csd);
                        break;
                    default:
                        throw new AssertionError(i18n("GERR_ILLEGAL_STATE"));
                }
            } else if (diagram instanceof PrimarySpiderDiagram) {
                drawPrimaryDiagram((PrimarySpiderDiagram) diagram);
            } else if (diagram instanceof NullSpiderDiagram) {
                drawNullSpiderDiagram();
            } else {
                throw new IllegalArgumentException(i18n("SD_PANEL_UNKNOWN_DIAGRAM_TYPE"));
            }
        }
    }

    private void drawInfixDiagram(CompoundSpiderDiagram csd) throws CannotDrawException {
        if (csd != null && csd.getOperandCount() > 0) {
            int gridx = 0;
            diagrams.setLayout(new GridBagLayout());
            GridBagConstraints gridBagConstraints;
            
            // Now start adding the panels onto the surface
            Iterator<SpiderDiagram> sdIter = csd.getOperands().iterator();
            JPanel sdp = DiagramVisualisation.getSpiderDiagramPanel(sdIter.next());
            gridBagConstraints = getOperandLayoutConstraints(gridx, true, sdp.getPreferredSize().width, 1);
            diagrams.add(sdp, gridBagConstraints);

            while (sdIter.hasNext()) {
                gridBagConstraints = getOperandLayoutConstraints(++gridx, false, 0, 0);
                diagrams.add(new OperatorPanel(csd.getOperator()), gridBagConstraints);

                sdp = DiagramVisualisation.getSpiderDiagramPanel(sdIter.next());
                gridBagConstraints = getOperandLayoutConstraints(++gridx, true, sdp.getPreferredSize().width, 1);
                diagrams.add(sdp, gridBagConstraints);
            }

            refreshPrefSize();
        } else {
            throw new AssertionError(i18n("GERR_ILLEGAL_STATE"));
        }
    }

    private GridBagConstraints getOperandLayoutConstraints(int gridx, boolean fill, int weightx, int weighty) {
        GridBagConstraints gridBagConstraints;
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = gridx;
        gridBagConstraints.gridy = 0;
        gridBagConstraints.fill = fill ? java.awt.GridBagConstraints.BOTH : GridBagConstraints.NONE;
        gridBagConstraints.weightx = weightx;
        gridBagConstraints.weighty = weighty;
        return gridBagConstraints;
    }

    private void drawPrefixDiagram(CompoundSpiderDiagram csd) throws CannotDrawException {
        if (csd != null && csd.getOperandCount() == 1) {
            diagrams.add(new OperatorPanel(csd.getOperator()));
            diagrams.add(DiagramVisualisation.getSpiderDiagramPanel(csd.getOperands().get(0)));
            refreshPrefSize();
        } else {
            throw new AssertionError(i18n("GERR_ILLEGAL_STATE"));
        }
    }

    private void drawPrimaryDiagram(PrimarySpiderDiagram psd) throws CannotDrawException {
        if (psd == null) {
            throw new AssertionError(i18n("GERR_ILLEGAL_STATE"));
        } else {
            diagrams.setLayout(new GridBagLayout());
            GridBagConstraints gbc = new java.awt.GridBagConstraints();
            diagrams.add(DiagramVisualisation.getSpiderDiagramPanel(psd), gbc);
            refreshPrefSize();
        }
    }

    private void drawNullSpiderDiagram() {
        diagrams.setLayout(new GridBagLayout());
        GridBagConstraints gbc = new java.awt.GridBagConstraints();
        final NullSpiderDiagramPanel nullSpiderDiagramPanel = new NullSpiderDiagramPanel();
        diagrams.add(nullSpiderDiagramPanel, gbc);
        refreshPrefSize();
    }

    private void refreshPrefSize() {
        Dimension prefSize = new Dimension();
        for (Component component : diagrams.getComponents()) {
            final Dimension curPrefSize = component.getPreferredSize();
            prefSize.height = Math.max(prefSize.height, curPrefSize.height);
            prefSize.width += curPrefSize.width;
        }
        prefSize.height += 10;
        prefSize.width += 10;
        setPreferredSize(prefSize);
        invalidate();
//        System.out.println("The preferred size: " + diagrams.getLayout().preferredLayoutSize(diagrams).toString());
//        setPreferredSize(diagrams.getLayout().preferredLayoutSize(diagrams));
    }
    // </editor-fold>
}
