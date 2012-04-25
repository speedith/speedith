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
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.InferenceRules;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.SplitSpiders;
import speedith.openproof.driver.SpiderDriver;
import speedith.ui.rules.InteractiveRuleApplication;
import speedith.ui.selection.helpers.DiagramSelector;

public class UnarySpidersRule extends OPDInferenceRule {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	private InferenceRule inferenceRule;
	
	public UnarySpidersRule(String speedithRuleName) {
		inferenceRule = InferenceRules.getInferenceRule(speedithRuleName);
	}
	
	public InferenceRule<SpiderRegionArg> getSpeedithRule() { return inferenceRule; }
	
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
		
		Goals goals = Goals.createGoalsFrom(citedDiagram);
		
		goals = Goals.createGoalsFrom(SpiderDiagrams.createCompoundSD(Operator.Implication,
					goals.getGoalAt(0), SpiderDiagrams.createNullSD()));
		
		if (arg == null) {
			try {
				arg = InteractiveRuleApplication.collectArgument(null, inferenceRule, 0, goals);
			} catch (RuntimeException e) { // TODO Make a specific user cancelled exception.
				return new OPDStatusObject(OPDStatusObject.OPDUntested, "User Cancelled", "User Cancelled");
			}
		}
		
		RuleApplicationResult applicationResult = null;
		
		SpiderDiagram result = null;
		
		try {
			applicationResult = inferenceRule.apply(arg, goals);
			result = ((CompoundSpiderDiagram) applicationResult.getGoals().getGoalAt(0)).getOperand(0);
		} catch (Exception ex) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, ex.getLocalizedMessage(), ex.getLocalizedMessage());
		}
		
		OPDStepInfo info = step.getRepresentation();
		info.getDriver().setDriverInfo(new Object[] { result, arg });
		
		return new OPDStatusObject(OPDStatusObject.OPDValid, "", "");
	}
}
