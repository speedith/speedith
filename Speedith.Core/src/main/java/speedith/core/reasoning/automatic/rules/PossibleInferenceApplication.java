package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;

/**
 * An instance of a possible inference application to an
 * Euler Diagram. The inference has not yet been applied to
 * the diagram, but the structure of the diagram would
 * allow the inference to be applied.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class PossibleInferenceApplication<TRuleArg extends RuleArg> {

    private final Inference<TRuleArg,?> inference;

    private final SpiderDiagramOccurrence target;

    private final int subGoalIndex;

    public PossibleInferenceApplication(int subGoalIndex, SpiderDiagramOccurrence target, InferenceRule<TRuleArg> inference) {
        this.target = target;
        this.inference = inference;
        this.subGoalIndex = subGoalIndex;
    }

    /**
     * The inference that could be applied.
     * @return an instance of the inference
     */
    public Inference<TRuleArg,?> getInference() { return inference; }

    /**
     * The target diagram to which the inference could be applied
     * @return the target diagram
     */
    public SpiderDiagramOccurrence getTarget() { return target; }

    public int getSubGoalIndex() {
        return subGoalIndex;
    }

    public abstract TRuleArg getArg() ;

    public boolean apply(Proof p, String typeSpecifier) throws RuleApplicationException {
        p.applyRule(getInference(), getArg(), RuleApplicationType.AUTOMATIC, typeSpecifier);
        return true;
    }


    /**
     * Check whether there is already an application of a proof inference within
     * p that makes this proof inference application superfluous, or worse the entrance
     * to an infinite loop. The standard implementation always returns false, i.e., the
     * inference application is not superfluous.
     *
     * NOTE: The standard implementation always returns false
     *
     * @param p a proof
     * @return true, if the inference application would be superfluous
     */
    public boolean isSuperfluous(Proof p) {
        return false;
    }
}
