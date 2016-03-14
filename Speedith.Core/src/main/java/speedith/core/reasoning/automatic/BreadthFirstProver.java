package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofTrace;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;
import speedith.core.reasoning.automatic.strategies.NoStrategy;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.util.AutomaticUtils;

import java.util.*;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class BreadthFirstProver extends  AutomaticProver {

    private static final String proverName = "breadth_first";

    public BreadthFirstProver() {super(new NoStrategy());}

    public BreadthFirstProver(Strategy strategy) {
        super(strategy);
    }

    @Override
    protected Proof prove(Proof p, int subgoalindex) throws RuleApplicationException, AutomaticProofException {
        p = tryToFinish(p, subgoalindex);
        if (p.isFinished()) {
            return p;
        }
        // initialise the set of proofs to be considered
        Set<ProofTrace> currentProofs = new HashSet<>();
        Set<ProofTrace> closed = new HashSet<>();
        currentProofs.add((ProofTrace) p);
        // initialise the new set of proofs
        Set<ProofTrace> newProofs ;
        Map<ProofTrace, AppliedRules> rulesWithinProofs = new HashMap<>();
        rulesWithinProofs.put((ProofTrace) p, new AppliedRules());

         Goals currentGoals = p.getLastGoals();
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<>();
        for (SpiderDiagram sd : currentGoals.getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        Proof finishedProof = null;
        long startTime= System.nanoTime();
        while(finishedProof == null && !currentProofs.isEmpty() && !Thread.currentThread().isInterrupted()) {
            newProofs = new HashSet<>();
            for(ProofTrace current : currentProofs) {
                current = (ProofTrace) tryToFinish(current, subgoalindex);
                if (current.isFinished()) {
                    // we found a finished proof
                    finishedProof = current;
                    break;
                } else {
                    // create all possible proof rules for this unfinished proof
                    SpiderDiagramOccurrence target = SpiderDiagramOccurrence.wrapDiagram(current.getLastGoals().getGoalAt(subgoalindex), 0);
                   Set<? extends PossibleRuleApplication<? extends RuleArg>> applications = AutomaticUtils.createAllPossibleRuleApplications(target, contours);
                    // apply all possible rules to the current proof, creating a new proof for each application
                    for (PossibleRuleApplication nextRule : applications ){
                        ProofTrace newCurrent = new ProofTrace(current.getGoals(), current.getRuleApplications());
                        // create a new set of already applied rules for the current proof
                        AppliedRules alreadyApplied = new AppliedRules(rulesWithinProofs.get(current));
                        boolean hasbeenApplied = nextRule.apply(newCurrent, subgoalindex, alreadyApplied, getPrettyName());
                        if (hasbeenApplied) {
                            // save the new proof within the set of not yet considered proofs
                            newProofs.add(newCurrent);
                            // save the rules that have already been applied for the new proof
                            rulesWithinProofs.put(newCurrent,alreadyApplied);
                        }
                    }
                }
                // remove the applied rules for this proof (since we create a new proof for each step)
                rulesWithinProofs.remove(current);
                closed.add(current);
            }
            // the new set of not yet considered proofs
            currentProofs = newProofs;
        }
        System.out.println("Considered "+closed.size()+ " proof attempts");
        long duration = System.nanoTime() - startTime;
        System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms");
        System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed.size() +"ms\n");
        return finishedProof;
    }

    @Override
    public AutomaticProver getAutomaticProver() {
        return this;
    }

    @Override
    public String getAutomaticProverName() {
        return proverName;
    }

    @Override
    public String getDescription() {
        return "Breadth first proof search";
    }

    @Override
    public String getPrettyName() {
        return "Breadth First";
    }
}
