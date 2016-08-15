package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofTrace;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;
import speedith.core.reasoning.automatic.strategies.NoStrategy;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.HeuristicsComparator;
import speedith.core.reasoning.automatic.wrappers.ProofAttempt;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.util.AutomaticUtils;
import speedith.core.reasoning.tactical.TacticApplicationException;

import java.text.DecimalFormat;
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


    /**
     * Creates an instance of the heuristic prover without a certain strategy, i.e.,
     * with a strategy that does not distinguish the costs of proof attempts.
     *
     */
    public HeuristicSearch() {super(new NoStrategy());}

    /**
     * Creates an instance of the heuristic prover with the certain strategy.
     * @param strategy The strategy that the provers uses to order proof attempts
     */
    public HeuristicSearch(Strategy strategy) {
        super(strategy);
    }

    @Override
    protected Proof prove(Proof p, int subgoalindex) throws RuleApplicationException, TacticApplicationException, AutomaticProofException {
        p = tryToFinish(p, subgoalindex);
        if (p.isFinished()) {
            return p;
        }
        // the set of already visited proofs (not necessary for the algorithm itself, but nice for
        // getting a clue how many proofs have been analysed)
        //Set<ProofAttempt> closed = new HashSet<>();

        //the number of analysed proof attempts (for statistics)
        int closed = 0;

        // the list of proof attempts, which still have to be visited
        PriorityQueue<ProofAttempt> attempts = new PriorityQueue<>(11, new HeuristicsComparator());
        ProofAttempt pw = new ProofAttempt(p,getStrategy());
        attempts.add(pw);
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<>();
        for (SpiderDiagram sd : p.getLastGoals().getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        long numOfSuperFl = 0;
        long startTime= System.nanoTime();
        while(!attempts.isEmpty() && !Thread.currentThread().isInterrupted()) {
            ProofAttempt currentAttempt = attempts.poll();
            Proof currentProof = tryToFinish(currentAttempt.getProof(), subgoalindex);
            if (currentProof.isFinished()) {
                //TODO: remove sysout
                printStatistics(closed, attempts,startTime, numOfSuperFl);
                return currentProof;
            }
            SpiderDiagramOccurrence target = SpiderDiagramOccurrence.wrapDiagram(currentProof.getLastGoals().getGoalAt(subgoalindex), 0);
            Set<? extends PossibleRuleApplication<? extends RuleArg>> applications = AutomaticUtils.createAllPossibleRuleApplications(subgoalindex, target, contours);
            // apply all possible rules to the current proof, creating a new proof for each application
            for(PossibleRuleApplication nextRule : applications) {
                ProofTrace newCurrent = new ProofTrace(currentProof.getGoals(), currentProof.getInferenceApplications());
                boolean superfl = nextRule.isSuperfluous(newCurrent);
                if (superfl) numOfSuperFl++;
                boolean hasBeenApplied =  /*!superfl  && */nextRule.apply(newCurrent, getPrettyName());
                if (hasBeenApplied) {
                    // save the new proof within the set of not yet considered proofs
                    ProofAttempt newAttempt = new ProofAttempt(newCurrent, getStrategy());
                    attempts.add(newAttempt);
                }
            }
            attempts.remove(currentAttempt);
            closed++;
        }
        // TODO: remove sysout
        printStatistics(closed, attempts,startTime,numOfSuperFl);
        return null;
    }

    private void printStatistics(int closed, Collection<ProofAttempt> attempts, long startTime, long superfluousAttemps) {
        long duration = System.nanoTime() - startTime;
        DecimalFormat format = new DecimalFormat("###,###,###,###");
        String fullNumber= format.format(closed+attempts.size());
        String considered = format.format(closed);
        String superfluous = format.format(superfluousAttemps);
        System.out.println("Prover: "+getPrettyName());
        System.out.println("Considered proof attempts: "+considered);
        System.out.println("Complete number of created proofs: "+fullNumber);
        System.out.println("Number of prevented rule applications: "+superfluous);
        System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms ("+ TimeUnit.NANOSECONDS.toSeconds(duration)+"s)" );
        System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed +"ms\n");
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
