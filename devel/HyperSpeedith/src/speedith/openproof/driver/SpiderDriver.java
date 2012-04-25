package speedith.openproof.driver;

import java.util.ArrayList;
import java.util.Collection;

import openproof.zen.OpenproofFace;
import openproof.zen.Precondition;
import openproof.zen.proofdriver.OPDGoal;
import openproof.zen.proofdriver.OPDGoalRule;
import openproof.zen.proofdriver.OPDProofDriver;
import openproof.zen.proofdriver.OPDStatusObject;
import openproof.zen.proofdriver.OPDStep;
import openproof.zen.repdriver.IllFormedRepresentationException;
import openproof.zen.repdriver.OPDRepDriver;
import openproof.zen.repeditor.OPERepEditor;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.reasoning.args.RuleArg;
import speedith.openproof.editor.SpiderInternalEditor;
import speedith.ui.SpeedithMainForm;

public class SpiderDriver implements OPDRepDriver, Cloneable {
	public static final String REPRESENTATION_NAME = "speedith";
	public static final Precondition[] PRECONDITIONS = null;
	
	private SpiderDiagram diagram;
	private RuleArg ruleArgument;
	
	
	private OPDStep step;
	private OPDGoal goal;
	
	private SpiderInternalEditor editor;
	
	public SpiderDriver() {
		diagram = SpiderDiagrams.createNullSD();
		ruleArgument = null;
	}
	
	public Object[] getDriverInfo() { return new Object[] { diagram, ruleArgument }; }
	
	public void setDriverInfo(Object objs[]) {
		diagram = (SpiderDiagram) objs[0];
		ruleArgument = (RuleArg) objs[1];
	}
	
	public OPDRepDriver getHeadDriver() { return this; }
	
	public void aboutToSave(boolean pad) { }
	public void closingRepresentation() { }
	public Object getClipboardData() { return diagram.toString(); }
	
	public void setStep(OPDStep sstep) { this.step = sstep; }
	public OPDGoal getGoal() { return goal; }
	public void setGoal(OPDGoal goal) { this.goal = goal; }
	
	public String getInfoText() { return null; }

	public String getInternalRepName() { return REPRESENTATION_NAME; }

	public Collection getNamesInUse() { return new ArrayList(); }

	public void initDriver(OPDProofDriver opd) { }

	public boolean isAutoConsistent() { return false; }
	public boolean isFalse() { return false; }

	public boolean isEmpty() { return diagram instanceof NullSpiderDiagram; }  
	
	public boolean isHeadless() { return false; }

	public boolean representationIsWellFormed() throws IllFormedRepresentationException {
		if (diagram.isValid())
			return true;
		else
			throw new IllFormedRepresentationException("Spider diagram is invalid.", new OPDStatusObject(OPDStatusObject.OPDBadForm, "", ""));
	}

	public void resolveClipboardData(OPDStep pasteStep, Object repData) {
		throw new RuntimeException("Paste not supported for spider diagrams.");
	}
	
	public SpiderDriver clone() {
		try {
			return (SpiderDriver) super.clone();
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * Returns null.
	 * 
	 * @deprecated  The moment that this method is removed from the parent
	 *              intereface, you should remove it here.
	 */
	public OpenproofFace getOpenproof() { return null; }
	
	/**
	 * Returns null.
	 * 
	 * @deprecated  The moment that this method is removed from the parent
	 *              intereface, you should remove it here.
	 */
	public Object getSaveInfo() { return null; }

	public void openproofBeanStart(OpenproofFace openproof, boolean headLess) { }

	public void openproofBeanUIStart(OpenproofFace openproof, boolean headLess) { }
	
	public OPERepEditor createGoalSpecEditor(OPDGoalRule rule, boolean force) { return null; }
	public void deinstallConstraintsEditor(Object o) { }
	public void installConstraintsEditor(Object o) { }

	public Object installRepEditor(OPERepEditor o) { 
		this.editor = (SpiderInternalEditor) o;
		
		if (this.editor == null)
			this.editor = new SpiderInternalEditor();
		
		return this.editor;
	}

	public boolean isDefault() { return false; }

	public String getRepresentationName() { return REPRESENTATION_NAME; }
}
