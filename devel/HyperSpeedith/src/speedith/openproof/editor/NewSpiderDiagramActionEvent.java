package speedith.openproof.editor;

import java.awt.Container;
import java.awt.Rectangle;

import javax.swing.JFrame;

import openproof.zen.EditorFrame;
import openproof.zen.proofeditor.NewDiagramActionEvent;
import openproof.zen.proofeditor.OPEStepInfo;
import openproof.zen.proofeditor.SimpleStepFace;
import speedith.openproof.driver.SpiderDriver;

public class NewSpiderDiagramActionEvent extends NewDiagramActionEvent {
	public NewSpiderDiagramActionEvent(Object source, int id, String command) {
		super(source, id, command);
	}

	@Override
	public void execute(Container ppv, SimpleStepFace focusStep, EditorFrame editor) {
		String ss = editor.getExternalRepName(SpiderDriver.REPRESENTATION_NAME);
		
		if (ss != null) {
			OPEStepInfo opeStepInfo = focusStep.createNewStepInfo(SpiderDriver.REPRESENTATION_NAME, null);
			if (null == opeStepInfo) return;
			
			SpiderInternalEditor stepEdit = (SpiderInternalEditor) opeStepInfo.getOPEEditor();
			
			SpiderExternalEditor sitEdit = (SpiderExternalEditor) stepEdit.getRepEditor();
			JFrame f = sitEdit.showFrame();

			Rectangle r = mainFrameBounds(ppv);
			f.setLocation(r.x+r.width, r.y);
			f.setSize(r.width, r.width-200); // hack!  Make it as wide as the proof window, and a pleasing height.

			sitEdit.setVisible(true);

			focusStep.attachRepresentation(opeStepInfo);
		} else {
			throw new RuntimeException("Unable to find representation for internal name " + ss);
		}
	}
}
