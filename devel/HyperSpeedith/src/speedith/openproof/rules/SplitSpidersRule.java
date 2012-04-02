package speedith.openproof.rules;

import java.util.Iterator;

import openproof.zen.Precondition;
import openproof.zen.proofdriver.OPDInferenceRule;
import openproof.zen.proofdriver.OPDProof;
import openproof.zen.proofdriver.OPDSimpleStep;
import openproof.zen.proofdriver.OPDStatusObject;
import openproof.zen.proofdriver.OPDStepInfo;
import openproof.zen.proofdriver.OPDSupportPack;
import openproof.zen.repdriver.OPDRepDriver;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.openproof.driver.SpiderDriver;
import speedith.ui.selection.helpers.DiagramSelector;

public class SplitSpidersRule extends OPDInferenceRule {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	private InferenceRule<SpiderRegionArg> splitSpiders = (InferenceRule<SpiderRegionArg>) InferenceRules.getInferenceRule(SplitSpiders.InferenceRuleName);
	
	static {
		Iterator<String> itr = InferenceRules.getKnownInferenceRules().iterator();
		
		while (itr.hasNext()) {
			System.out.println(itr.next());
		}
	}
	
	public InferenceRule<SpiderRegionArg> getSpeedithRule() { return splitSpiders; }
	
	/**
	 * @return  The name of the representation that is inferred by this inference rule.
	 */
	public String getInferredRepName() { return REPRESENTATION_NAME; }
	
	public OPDStatusObject check(OPDSimpleStep step) {
		if (step.getSupport().size() != 1) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for split spiders.",
																	"Exactly one spider diagram must be cited for split spiders.");
		}
		
		OPDSupportPack d = step.getSupport().elementAt(0);
		
		if (d.getOPDStep() instanceof OPDProof) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for split spiders.",
																	"Exactly one spider diagram must be cited for split spiders.");
		}
		
		OPDRepDriver driver = d.getOPDStepInfo().getDriver();
		
		if (driver instanceof SpiderDriver == false) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one spider diagram must be cited for split spiders.",
																	"Exactly one spider diagram must be cited for split spiders.");
		}
		
		SpiderDiagram citedDiagram = (SpiderDiagram) ((SpiderDriver) driver).getDriverInfo()[0];
		
		RuleArg arg = null;
		
		if (step.getRepresentation().getDriver() instanceof SpiderDriver) {
			arg =  (RuleArg) step.getRepresentation().getDriver().getDriverInfo()[1];
		}
		
		SpiderRegionArg feetArg;
		
		if (arg instanceof SpiderRegionArg) {
			feetArg = (SpiderRegionArg) arg;
		} else {
			feetArg = DiagramSelector.getSelector(SpiderRegionArg.class).showSelectionDialog(null, citedDiagram);
		}
		
		RuleApplicationResult applicationResult = null;
		
		if (feetArg != null) {
			try {
				applicationResult = splitSpiders.apply(feetArg, Goals.createGoalsFrom(citedDiagram));
			} catch (Exception ex) {
				return new OPDStatusObject(OPDStatusObject.OPDInvalid, ex.getLocalizedMessage(), ex.getLocalizedMessage());
			}
		} else {
			return new OPDStatusObject(OPDStatusObject.OPDUntested, "User Cancelled", "User Cancelled");
		}
		
		OPDStepInfo info = step.getRepresentation();
		info.getDriver().setDriverInfo(new Object[] { applicationResult.getGoals().getGoalAt(0), feetArg });
		
		return new OPDStatusObject(OPDStatusObject.OPDValid, "", "");
	}
}
