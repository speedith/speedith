/*
 *   Project: Speedith
 * 
 * File name: PrimarySpiderDiagramPanel.java
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
 * PrimarySpiderDiagramPanel.java
 *
 * Created on 29-Sep-2011, 11:53:13
 */
package speedith.draw;

import icircles.gui.CirclesPanel;
import java.awt.BorderLayout;
import icircles.util.CannotDrawException;
import javax.swing.JLabel;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import static speedith.i18n.Translations.*;

/**
 * This panel displays {@link PrimarySpiderDiagram primary spider diagrams}.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class PrimarySpiderDiagramPanel extends javax.swing.JPanel {

    /** Creates new form PrimarySpiderDiagramPanel */
    public PrimarySpiderDiagramPanel() {
        initComponents();
    }

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        setBackground(new java.awt.Color(255, 255, 255));
        setLayout(new java.awt.BorderLayout());
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    // End of variables declaration//GEN-END:variables
    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private PrimarySpiderDiagram diagram;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the currently presented diagram.
     * <p>May be {@code null}, which indicates that the panel is empty.</p>
     * @return the currently presented diagram, or {@code null} is no diagram
     * is currently being shown.
     */
    public PrimarySpiderDiagram getDiagram() {
        return diagram;
    }

    /**
     * Sets the currently shown diagram.
     * <p>May be {@code null}, which indicates that the panel should
     * be empty.</p>
     * @param diagram the new diagram to show, or {@code null} if no diagram is
     * to be shown.
     */
    public void setDiagram(PrimarySpiderDiagram diagram) {
        if (this.diagram != diagram) {
            this.diagram = diagram;
            this.removeAll();
            if (this.diagram != null) {
                javax.swing.JComponent component;
                try {
                    component = DiagramVisualisation.getSpiderDiagramPanel(this.diagram);
                    component.setSize(200, 200);
                } catch (CannotDrawException ex) {
                    JLabel errorLabel = new JLabel();
                    errorLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
                    errorLabel.setText(i18n("PSD_LABEL_DISPLAY_ERROR"));
                    component = errorLabel;
                }
                add(component, BorderLayout.CENTER);
            }
        }
    }

    /**
     * Returns the string representation of the currently shown diagram.
     * @return the string representation of the currently shown diagram.
     */
    public String getDiagramString() {
        return this.diagram == null ? "" : this.diagram.toString();
    }

    /**
     * Sets the currently shown diagram via its string representation.
     * <p>This method tries to parse the string into a spider diagram and
     * draws it.</p>
     * <p>Here is an example of a valid string:
     * <pre>"PrimarySD {spiders = ["s1", "s2", "s3"], habitats = [("s1", [(["A"], ["B", "C"]), (["A", "B"], ["C"]), (["A", "B", "C"], [])]), ("s2", [(["B"], ["A", "C"])]), ("s3", [(["B"], ["A", "C"])])], sh_zones = [(["B"], ["A", "C"])]}"</pre>
     * </p>
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
            SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram(diagram);
            if (sd instanceof PrimarySpiderDiagram) {
                setDiagram((PrimarySpiderDiagram) sd);
            } else {
                throw new IllegalArgumentException(i18n("PSD_PANEL_INVALID_DIAGRAM_STRING"));
            }
        }
    }
    // </editor-fold>
}
