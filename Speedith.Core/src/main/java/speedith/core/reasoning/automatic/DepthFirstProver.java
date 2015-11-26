package speedith.core.reasoning.automatic;

import speedith.core.lang.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.CompoundSpiderDiagramWrapper;
import speedith.core.reasoning.automatic.wrappers.PrimarySpiderDiagramWrapper;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.*;
import speedith.core.reasoning.rules.util.AutomaticUtils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * Generates proofs for given subgoals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 * Created by sl542 on 11/11/15.
 *
 */
public class DepthFirstProver extends AutomaticProver {


    public DepthFirstProver(Strategy strategy) {
        super(strategy);
    }

    /**
     * Creates a proof without possibilities to set the wanted
     * heuristics using a depth-first search.
     *
     * Recursively create and apply all rule applications for the given subgoal  in the current
     * state of the given Proof p. The rules already applied to subdiagrams within
     * the current set of goals are saved in appliedRules
     */
    @Override
    protected Proof prove(Proof p, int subgoalindex, AppliedRules appliedRules) throws RuleApplicationException {
        p = tryToFinish(p, subgoalindex);
        if (p.isFinished()) {
            return p;
        }
        Goals currentGoals = p.getLastGoals();
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<String>();
        for (SpiderDiagram sd : currentGoals.getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        SpiderDiagramWrapper target = wrapDiagram(currentGoals.getGoalAt(subgoalindex), 0);
        Set<PossibleRuleApplication> applications = AutomaticUtils.createAllPossibleRuleApplications(target, contours, appliedRules);
        PossibleRuleApplication nextRule = null;
        do  {
            nextRule = getStrategy().select(p, applications);
            boolean hasbeenApplied = nextRule != null && nextRule.apply(p, subgoalindex, appliedRules);
            if (hasbeenApplied) {
                p = prove(p, subgoalindex, appliedRules);
                if (p.isFinished()) {
                    return p;
                }
                p.undoStep();
            }
        } while(nextRule != null);

        return p;
    }

}
