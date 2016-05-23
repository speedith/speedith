package speedith.core.reasoning.automatic.rules;

import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.ConjunctionElimination;

import java.util.ArrayList;
import java.util.List;

/**
 * A possibility to apply conjunction elimination.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class PossibleConjunction extends PossibleRuleApplication<MultipleRuleArgs> {
    final SpiderDiagramOccurrence child;
    public PossibleConjunction(int subGoalIndex, SpiderDiagramOccurrence target, ConjunctionElimination rule, SpiderDiagramOccurrence child) {
        super(subGoalIndex, target, rule);
        this.child = child;
    }

    @Override
    public MultipleRuleArgs getArg() {
        SubDiagramIndexArg compound  = new SubDiagramIndexArg(getSubGoalIndex(), getTarget().getOccurrenceIndex());
        SubDiagramIndexArg childArg = new SubDiagramIndexArg(getSubGoalIndex(), child.getOccurrenceIndex());
        List<SubDiagramIndexArg> args = new ArrayList<>();
        args.add(compound);
        args.add(childArg);
        return new MultipleRuleArgs(args);
    }
}
