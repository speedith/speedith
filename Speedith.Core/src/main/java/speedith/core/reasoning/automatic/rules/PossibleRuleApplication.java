package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationType;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;

/**
 * An instance of a possible rule application to an
 * Euler Diagram. The rule has not yet been applied to
 * the diagram, but the structure of the diagram would
 * allow the rule to be applied.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class PossibleRuleApplication {

    private final InferenceRule<? super RuleArg> rule;

    private final SpiderDiagramOccurrence target;

    public PossibleRuleApplication(SpiderDiagramOccurrence target, InferenceRule<? super RuleArg> rule) {
        this.target = target;
        this.rule = rule;
    }

    /**
     * The rule that could be applied.
     * @return an instance of the rule
     */
    public InferenceRule<? super RuleArg> getRule() { return rule; }

    /**
     * The target diagram to which the rule could be applied
     * @return the target diagram
     */
    public SpiderDiagramOccurrence getTarget() { return target; }

    public abstract RuleArg getArg(int subgoalindex) ;

    public boolean apply (Proof p, int subGoalIndex, AppliedRules applied, String typeSpecifier) throws RuleApplicationException {
        p.applyRule(getRule(), getArg(subGoalIndex), RuleApplicationType.AUTOMATIC, typeSpecifier);
        return true;
    }


    /**
     * Check whether there is already an application of a proof rule within
     * p that makes this proof rule application superfluous, or worse the entrance
     * to an infinite loop. The standard implementation always returns false, i.e., the
     * rule application is not superfluous.
     *
     * NOTE: The standard implementation always returns false
     *
     * @param p a proof
     * @param subGoalIndex the subgoal index the proof rule shall be applied to
     * @return true, if the rule application would be superfluous
     */
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        return false;
    }
}
