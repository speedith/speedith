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

    private InferenceRule<? super RuleArg> rule;

    private SpiderDiagramOccurrence target;

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

    public boolean apply (Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
        p.applyRule(getRule(), getArg(subGoalIndex), RuleApplicationType.AUTOMATIC);
        return true;
    }

    /**
     * Remove this {@link PossibleRuleApplication possible rule application } from the set of
     * already applied rules.
     * The standard implementation does nothing!
     *
     * @param applied the set of applied rules this instance will be removed from
     */
    public void removeFrom(AppliedRules applied) {}

    /**
     * Check whether there is already an application of a proof rule within
     * p that makes this proof rule application superfluous, or worse the entrance
     * to an infinite loop. The standard implementation always returns false, i.e., the
     * rule application is not superfluous.
     * @param p
     * @param subGoalIndex
     * @return
     */
    public boolean isSuperfluous(Proof p, int subGoalIndex) {
        return false;
    }
}
