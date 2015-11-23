package speedith.core.reasoning.automatic;

import org.antlr.tool.Rule;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;

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

    private SpiderDiagram target;

    public PossibleRuleApplication(SpiderDiagram target, InferenceRule<? super RuleArg> rule) {
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
    public SpiderDiagram getTarget() { return target; }

    public abstract RuleArg getArg(int subgoalindex, SpiderDiagram sd) throws RuleApplicationException;
}