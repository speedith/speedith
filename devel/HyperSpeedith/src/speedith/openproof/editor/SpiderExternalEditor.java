package speedith.openproof.editor;

import java.awt.Color;

import javax.swing.JFrame;

import openproof.awt.OPUndoManager;
import openproof.zen.repeditor.ChangeReporter;
import openproof.zen.repeditor.DiagrammaticRepresentationEditor;
import speedith.core.lang.SpiderDiagram;
import speedith.ui.SpiderDiagramPanel;

public class SpiderExternalEditor extends SpiderDiagramPanel implements DiagrammaticRepresentationEditor {
	public Color getBackgroundColor() { return null; }

	public String getTitle() { return "Spider Editor"; }
	public void init(Color bgcolor) { }

	public void setBackgroundColor(Color bgcolor) { }
	
	/**
	 * Object o must be an array with one element, which is a SpiderDiagram
	 */
	public void setEditorInfo(Object o, boolean redraw, boolean focusStep) {
		if (!focusStep) return;
		
		SpiderDiagram d = (SpiderDiagram) ((Object[]) o)[0];
		setDiagram(d);
	}

	public void setReporter(ChangeReporter r) { }

	public void setUndoManager(OPUndoManager undoManager) { }

	public boolean testAndClearInScopeFF() { return false; }
	public boolean testAndSetInScopeFF() { return true; }
	public boolean testInScopeFF() { return false; }
	public void clearInScopeFF() { }
	
	/**
	 * Display a JFrame which contains the panel.
	 * Returns the JFrame.
	 */
	public JFrame showFrame() {
		JFrame f = new JFrame("Spider");
		
		f.setSize(100, 100);
		f.getContentPane().add(this);
		f.pack();
		f.setVisible(true);
		
		return f;
	}
}
