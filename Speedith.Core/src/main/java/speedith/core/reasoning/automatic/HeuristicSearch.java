package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofTrace;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;
import speedith.core.reasoning.automatic.strategies.NoStrategy;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.ProofAttempt;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.util.AutomaticUtils;

import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * Implements an A* search with the heuristic strategy currently loaded within
 * Speedith.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class HeuristicSearch extends AutomaticProver {

    private static final String proverName = "heuristic";


    public HeuristicSearch() {super(new NoStrategy());}

    public HeuristicSearch(Strategy strategy) {
        super(strategy);
    }

    @Override
    protected Proof prove(Proof p, int subgoalindex) throws RuleApplicationException, AutomaticProofException {
        p = tryToFinish(p, subgoalindex);
        if (p.isFinished()) {
            return p;
        }
        // the set of already visited proofs (not necessary for the algorithm itself, but nice for
        // getting a clue how many proofs have been analysed
        Set<ProofAttempt> closed = new HashSet<>();
        // the list of proof attempts, which still have to be visited
        List<ProofAttempt> attempts = new ArrayList<>();
        ProofAttempt pw = new ProofAttempt(p,getStrategy());
        attempts.add(pw);
        // the rules that have already been applied to the subgoals
        AppliedRules appliedRules = new AppliedRules();
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<>();
        for (SpiderDiagram sd : p.getLastGoals().getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        long startTime= System.nanoTime();
        while(!attempts.isEmpty()) {
            ProofAttempt currentAttempt = attempts.remove(0);
            Proof currentProof = tryToFinish(currentAttempt.getProof(), subgoalindex);
            if (currentProof.isFinished()) {
                //TODO: remove sysout
                System.out.println("Considered "+closed.size()+ " proof attempts");
                long duration = System.nanoTime() - startTime;
                System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms");
                System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed.size() +"ms\n");
                return currentProof;
            }
            Set<ProofAttempt> newProofs = new HashSet<>();
            SpiderDiagramWrapper target = wrapDiagram(currentProof.getLastGoals().getGoalAt(subgoalindex),0);
            Set<PossibleRuleApplication> applications = AutomaticUtils.createAllPossibleRuleApplications(target, contours, appliedRules);
            // apply all possible rules to the current proof, creating a new proof for each application
            for(PossibleRuleApplication nextRule : applications) {
                ProofTrace newCurrent = new ProofTrace(currentProof.getGoals(), currentProof.getRuleApplications());
                // create a new set of already applied rules for the current proof
//                long currentTime = System.nanoTime();
                boolean hasbeenApplied =  nextRule.apply(newCurrent, subgoalindex, appliedRules);
//                System.out.println("Took "+ TimeUnit.NANOSECONDS.toMillis(System.nanoTime()- currentTime)+"ms \t to apply rule"+ nextRule);
                if (hasbeenApplied) {
                    // save the new proof within the set of not yet considered proofs
                    ProofAttempt newAttempt = new ProofAttempt(newCurrent, getStrategy());
                    newProofs.add(newAttempt);
                }
            }
            closed.add(currentAttempt);
            attempts.addAll(newProofs);
            Collections.sort(attempts);
        }
        // TODO: remove sysout
        System.out.println("Considered "+closed.size()+ " proof attempts");
        long duration = System.nanoTime() - startTime;
        System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms");
        System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed.size() +"ms\n");
        return null;
    }

    @Override
    public AutomaticProver getAutomaticProver() {
        return this;
    }

    @Override
    public String getAutomaticProverName() {
        return proverName ;
    }

    @Override
    public String getDescription() {
        return "A* search with the currently selected strategy";
    }

    @Override
    public String getPrettyName() {
        return "Heuristic A* Search";
    }
}
