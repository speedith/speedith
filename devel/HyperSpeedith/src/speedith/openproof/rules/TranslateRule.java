package speedith.openproof.rules;

import java.io.UnsupportedEncodingException;

import openproof.fol.representation.OPFormula;
import openproof.fol.representation.parser.ParseException;
import openproof.foldriver.FOLDriver;
import openproof.zen.Precondition;
import openproof.zen.proofdriver.OPDInferenceRule;
import openproof.zen.proofdriver.OPDProof;
import openproof.zen.proofdriver.OPDSimpleStep;
import openproof.zen.proofdriver.OPDStatusObject;
import openproof.zen.proofdriver.OPDStepInfo;
import openproof.zen.proofdriver.OPDSupportPack;
import openproof.zen.repdriver.OPDRepDriver;
import speedith.openproof.driver.SpiderDriver;
import speedith.openproof.fol.ConversionException;
import speedith.openproof.fol.FOLToSpiders;

public class TranslateRule extends OPDInferenceRule {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	/**
	 * @return  The name of the representation that is inferred by this inference rule.
	 */
	public String getInferredRepName() { return REPRESENTATION_NAME; }
	
	public OPDStatusObject check(OPDSimpleStep step) {
		if (step.getSupport().size() != 1) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one FOL sentence must be cited for split spiders.",
																	"Exactly one FOL sentence must be cited for split spiders.");
		}
		
		OPDSupportPack d = step.getSupport().elementAt(0);
		
		if (d.getOPDStep() instanceof OPDProof) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one FOL sentence must be cited for split spiders.",
																	"Exactly one FOL sentence must be cited for split spiders.");
		}
		
		OPDRepDriver driver = d.getOPDStepInfo().getDriver();
		
		if (driver instanceof FOLDriver == false) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Exactly one FOL sentence must be cited for split spiders.",
																	"Exactly one FOL sentence must be cited for split spiders.");
		}
		
		try {
			OPFormula citedSentence = ((FOLDriver) driver).getFormula();
			
			OPDStepInfo info = step.getRepresentation();
			info.getDriver().setDriverInfo(new Object[] { FOLToSpiders.convert(citedSentence), null });
		} catch (UnsupportedEncodingException e) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Cited sentence is not well-formed.",
																	"Cited sentence is not well-formed.");
		} catch (ParseException e) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, "Cited sentence is not well-formed.",
																	"Cited sentence is not well-formed.");
		} catch (ConversionException e) {
			return new OPDStatusObject(OPDStatusObject.OPDInvalid, e.getLocalizedMessage(), e.getLocalizedMessage());
		}
		
		return new OPDStatusObject(OPDStatusObject.OPDValid, "", "");
	}
}
