package speedith.openproof.driver;

import java.awt.Color;

import openproof.zen.Precondition;
import openproof.zen.archive.OPClassInfo;
import openproof.zen.archive.OPDecoder;
import openproof.zen.archive.OPEncoder;
import openproof.zen.exception.OPCodingException;
import openproof.zen.proofdriver.OPDInferenceRuleList;
import openproof.zen.proofdriver.OPDRuleDriver;
import speedith.openproof.rules.ObserveRule;
import speedith.openproof.rules.SplitSpidersRule;
import speedith.openproof.rules.TranslateRule;

public class SpiderRuleDriver extends OPDRuleDriver {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	@Override
	public OPDInferenceRuleList createRules() {
		_fRules = new OPDInferenceRuleList(this, REPRESENTATION_NAME, REPRESENTATION_NAME, REPRESENTATION_NAME, null);
		
		SplitSpidersRule splitSpiders = new SplitSpidersRule();
		splitSpiders.set(this, splitSpiders.getSpeedithRule().getProvider().getInferenceRuleName(),
						splitSpiders.getSpeedithRule().getProvider().getPrettyName(),
						splitSpiders.getSpeedithRule().getProvider().getInferenceRuleName(),
						null, Color.red);
		
		ObserveRule observe = new ObserveRule();
		observe.set(this, "speedithObserve", "Observe", "Observe", null, Color.red);
		
		TranslateRule translate = new TranslateRule();
		translate.set(this, "speedithTranslate", "Translate", "Translate", null, Color.red);
		
		_fRules.addInferenceRule(splitSpiders);
		_fRules.addInferenceRule(observe);
		_fRules.addInferenceRule(translate);
		return _fRules;
	}

	@Override
	public String getDisplayRepName() { return "Speedith"; }

	@Override
	public String getInternalRepName() { return REPRESENTATION_NAME; }
	
	public void op_decode(OPDecoder decoder) throws OPCodingException { }
	public void op_describeClassInfo(OPClassInfo info) { }
	public void op_encode(OPEncoder encoder) throws OPCodingException { }
	public void op_finishDecoding() throws OPCodingException { }
}
