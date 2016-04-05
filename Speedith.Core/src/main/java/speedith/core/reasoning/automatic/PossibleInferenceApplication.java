package speedith.core.reasoning.automatic;

import speedith.core.reasoning.Inference;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationType;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.tactical.TacticApplicationException;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class PossibleInferenceApplication<TRuleArg extends RuleArg>  {

    private final Inference<TRuleArg,?> inference;

    private final int subGoalIndex;

    public PossibleInferenceApplication(int subGoalIndex, Inference<TRuleArg,?> inference) {
        this.inference = inference;
        this.subGoalIndex = subGoalIndex;
    }

    /**
     * The inference that could be applied.
     * @return an instance of the inference
     */
    public Inference<TRuleArg,?> getInference() { return inference; }

    public int getSubGoalIndex() {
        return subGoalIndex;
    }

    public abstract TRuleArg getArg() ;

    public boolean apply(Proof p, String typeSpecifier) throws RuleApplicationException, TacticApplicationException {
        p.applyRule(getInference(), getArg(), RuleApplicationType.AUTOMATIC, typeSpecifier);
        return true;
    }

}
