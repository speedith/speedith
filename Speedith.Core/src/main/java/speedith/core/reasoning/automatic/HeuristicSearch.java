package speedith.core.reasoning.automatic;

import propity.util.Sets;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;
import speedith.core.reasoning.automatic.strategies.NoStrategy;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.ProofAttempt;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.IntroShadedZone;
import speedith.core.reasoning.rules.RemoveContour;
import speedith.core.reasoning.rules.RemoveShadedZone;
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
        PriorityQueue<ProofAttempt> attempts = new PriorityQueue<>();
        ProofAttempt pw = new ProofAttempt(p,getStrategy());
        attempts.add(pw);
        // the rules that have already been applied to the subgoals
        AppliedRules appliedRules = new AppliedRules();
        Map<Proof, AppliedRules> applied = new HashMap<>();
        applied.put(p, appliedRules);
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<>();
        for (SpiderDiagram sd : p.getLastGoals().getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        long startTime= System.nanoTime();
        while(!attempts.isEmpty()) {
            ProofAttempt currentAttempt = attempts.poll();
            Proof currentProof = tryToFinish(currentAttempt.getProof(), subgoalindex);
            AppliedRules alreadyApplied = applied.get(currentProof);
            if (currentProof.isFinished()) {
                //TODO: remove sysout
                printStatistics(closed, startTime);
                return currentProof;
            }
            SpiderDiagramWrapper target = wrapDiagram(currentProof.getLastGoals().getGoalAt(subgoalindex),0);
            Set<PossibleRuleApplication> applications = AutomaticUtils.createAllPossibleRuleApplications(target, contours);
            // apply all possible rules to the current proof, creating a new proof for each application
            for(PossibleRuleApplication nextRule : applications) {
                ProofTrace newCurrent = new ProofTrace(currentProof.getGoals(), currentProof.getRuleApplications());
                // create a new set of already applied rules for the current proof
                AppliedRules updated = new AppliedRules(alreadyApplied);
                boolean hasBeenApplied =  !nextRule.isSuperfluous(newCurrent,subgoalindex) && nextRule.apply(newCurrent, subgoalindex, updated);
                if (hasBeenApplied) {
                    // save the new proof within the set of not yet considered proofs
                    ProofAttempt newAttempt = new ProofAttempt(newCurrent, getStrategy());
                    attempts.add(newAttempt);
                    applied.put(newCurrent, updated);
                } else {
//                    System.out.println("Did not apply "+ nextRule.getRule()+ " to occ index "+nextRule.getTarget().getOccurrenceIndex());
                }
            }
            applied.remove(currentProof);
            closed.add(currentAttempt);
        }
        // TODO: remove sysout
        printStatistics(closed, startTime);
        return null;
    }

    private void printStatistics(Set<ProofAttempt> closed, long startTime) {
        System.out.println("Considered "+closed.size()+ " proof attempts");
        long duration = System.nanoTime() - startTime;
        System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms ("+ TimeUnit.NANOSECONDS.toSeconds(duration)+"s)" );
        System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed.size() +"ms\n");
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
