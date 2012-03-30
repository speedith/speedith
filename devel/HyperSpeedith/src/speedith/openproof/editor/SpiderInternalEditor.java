package speedith.openproof.editor;

import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ImageIcon;

import openproof.zen.Precondition;
import openproof.zen.repeditor.DiagrammaticRepresentationEditor;
import openproof.zen.repeditor.OPEEmbeddedEditorAdapter;
import speedith.openproof.driver.SpiderDriver;

public class SpiderInternalEditor extends OPEEmbeddedEditorAdapter {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	private static SpiderExternalEditor extEditor = new SpiderExternalEditor();
	
	private static ImageIcon icns = new ImageIcon(Toolkit.getDefaultToolkit().getImage("SpeedithIconVennDiagram-32.png"));
	
	public SpiderInternalEditor() { }
	
	public Dimension getPreferredSize() { return new Dimension(32, 32); }
	
	public void displayIcon(boolean isAmbiguous) { }
	
	public String getRepresentationName() { return REPRESENTATION_NAME; }
	
	public void paint(Graphics g) {
		g.drawImage(icns.getImage(), 0, 0, this);
	}
	
	public DiagrammaticRepresentationEditor getRepEditor() { return extEditor; }
	
	/**
	 * This could be simplified by creating an action, but this would require Swing menu items
	 * which we currently don't have.
	 *
	 * @see openproof.zen.repeditor.DiagrammaticRepresentationEditor#getDiagramMenuItems()
	 */
	public Action[] getDiagramActions(final ActionListener al) {
		Action actions[] = new Action[1];
		
		actions[0] = new AbstractAction() {
			public void actionPerformed(ActionEvent e) {
				al.actionPerformed(new NewSpiderDiagramActionEvent(e.getSource(), 0, e.getActionCommand()));
			}
		};
		
		actions[0].putValue(Action.SHORT_DESCRIPTION, "New Spider Diagram");

		return actions;
	}
}
