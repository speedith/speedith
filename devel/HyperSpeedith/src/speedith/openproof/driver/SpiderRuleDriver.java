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
import speedith.openproof.rules.UnarySpidersRule;
import speedith.openproof.rules.TranslateRule;

public class SpiderRuleDriver extends OPDRuleDriver {
	public static final String REPRESENTATION_NAME = SpiderDriver.REPRESENTATION_NAME;
	public static final Precondition[] PRECONDITIONS = null;
	
	@Override
	public OPDInferenceRuleList createRules() {
		_fRules = new OPDInferenceRuleList(this, REPRESENTATION_NAME, REPRESENTATION_NAME, REPRESENTATION_NAME, null);
		
		ObserveRule observe = new ObserveRule();
		observe.set(this, "speedithObserve", "Observe", "Observe", null, Color.red);
		
		TranslateRule translate = new TranslateRule();
		translate.set(this, "speedithTranslate", "Translate", "Translate", null, Color.red);
		
		_fRules.addInferenceRule(createRule("add_feet"));
		_fRules.addInferenceRule(createRule("discharge_goal"));
		_fRules.addInferenceRule(createRule("idempotency"));
		_fRules.addInferenceRule(createRule("implication_tautology"));
		_fRules.addInferenceRule(createRule("split_spiders"));
		_fRules.addInferenceRule(observe);
		_fRules.addInferenceRule(translate);
		return _fRules;
	}

	private UnarySpidersRule createRule(String name) {
		UnarySpidersRule rule = new UnarySpidersRule(name);
		
		rule.set(this, "speedith" + rule.getSpeedithRule().getProvider().getInferenceRuleName(),
						rule.getSpeedithRule().getProvider().getPrettyName(),
						rule.getSpeedithRule().getProvider().getPrettyName(),
						null, Color.red);
		
		return rule;
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
