package speedith.openproof.rules;

import openproof.fol.representation.FOLRepresentation;
import openproof.fold.OPFOLRule;
import openproof.zen.Precondition;
import openproof.zen.proofdriver.OPDInferenceRule;
import openproof.zen.proofdriver.OPDProof;
import openproof.zen.proofdriver.OPDSimpleStep;
import openproof.zen.proofdriver.OPDStatusObject;
import openproof.zen.proofdriver.OPDSupportPack;
import openproof.zen.repdriver.OPDRepDriver;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.export.ExportException;
import speedith.core.lang.export.SDExporter;
import speedith.core.lang.export.SDExporting;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.openproof.driver.SpiderDriver;

public class ObserveRule extends OPDInferenceRule {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	private InferenceRule<SpiderRegionArg> splitSpiders = (InferenceRule<SpiderRegionArg>) InferenceRules.getInferenceRule(SplitSpiders.InferenceRuleName);
	
	public InferenceRule<SpiderRegionArg> getSpeedithRule() { return splitSpiders; }
	
	/**
	 * @return  The name of the representation that is inferred by this inference rule.
	 */
	public String getInferredRepName() { return FOLRepresentation.REPRESENTATION_NAME; }
	
	public OPDStatusObject check(OPDSimpleStep step) {
		if (step.getSupport().size() != 1) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for observe.",
																	"Exactly one spider diagram must be cited for observe.");
		}
		
		OPDSupportPack d = step.getSupport().elementAt(0);
		
		if (d.getOPDStep() instanceof OPDProof) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for observe.",
																	"Exactly one spider diagram must be cited for observe.");
		}
		
		OPDRepDriver driver = d.getOPDStepInfo().getDriver();
		
		if (driver instanceof SpiderDriver == false) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for observe.",
																	"Exactly one spider diagram must be cited for observe.");
		}
		
		SpiderDiagram citedDiagram = (SpiderDiagram) ((SpiderDriver) driver).getDriverInfo()[0];
		
		SDExporter exp = SDExporting.getExporter("Openproof");
		
		if (exp == null) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Could not convert spider diagram.", "Could not convert spider diagram.");
		}
		
		try {
			OPFOLRule.setText(step, exp.export(citedDiagram));
		} catch (ExportException e) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, e.getLocalizedMessage(), e.getLocalizedMessage());
		}
		
		return new OPDStatusObject(OPDStatusObject.OPDValid, "", "");
	}
}

