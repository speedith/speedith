package speedith.openproof.editor;

import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.image.BufferedImage;
import java.io.InputStream;
import javax.imageio.ImageIO;

import javax.swing.AbstractAction;
import javax.swing.Action;

import openproof.zen.Precondition;
import openproof.zen.repeditor.DiagrammaticRepresentationEditor;
import openproof.zen.repeditor.OPEEmbeddedEditorAdapter;
import speedith.openproof.driver.SpiderDriver;

public class SpiderInternalEditor extends OPEEmbeddedEditorAdapter {

	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	private static SpiderExternalEditor extEditor = new SpiderExternalEditor();
	private static BufferedImage icns;

	static {
		try {
			InputStream imgStream = SpiderInternalEditor.class.getResourceAsStream("/speedith/openproof/editor/SpeedithIconVennDiagram-32.png");
			icns = ImageIO.read(imgStream);
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}

	public SpiderInternalEditor() { }

	public Dimension getPreferredSize() { return new Dimension(32, 32); }

	public String getRepresentationName() { return REPRESENTATION_NAME; }

	public void paint(Graphics g) { g.drawImage(icns, 0, 0, this); }

	public DiagrammaticRepresentationEditor getRepEditor() { return extEditor; }

	/**
	 * This could be simplified by creating an action, but this would require
	 * Swing menu items which we currently don't have.
	 *
	 * @see
	 * openproof.zen.repeditor.DiagrammaticRepresentationEditor#getDiagramMenuItems()
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
