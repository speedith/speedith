package speedith.core.reasoning.automatic.rules;

import org.antlr.tool.Rule;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.AppliedRules;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;

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

    private SpiderDiagramWrapper target;

    public PossibleRuleApplication(SpiderDiagramWrapper target, InferenceRule<? super RuleArg> rule) {
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
    public SpiderDiagramWrapper getTarget() { return target; }

    public abstract RuleArg getArg(int subgoalindex) ;

    public boolean apply (Proof p, int subGoalIndex, AppliedRules applied) throws RuleApplicationException {
        p.applyRule(getRule(), getArg(subGoalIndex));
        return true;
    }

    /**
     * Remove this {@link PossibleRuleApplication possible rule application } from the set of
     * already applied rules.
     * The standard implementation does nothing!
     *
     * @param applied the set of applied rules this instance will be removed from
     */
    public void removeFrom(AppliedRules applied) {};
}
