package speedith.core.reasoning.automatic;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofTrace;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.automatic.rules.PossibleRuleApplication;
import speedith.core.reasoning.automatic.strategies.NoStrategy;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.tactical.PossibleTacticApplication;
import speedith.core.reasoning.automatic.wrappers.ProofAttempt;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.util.AutomaticUtils;
import speedith.core.reasoning.tactical.TacticApplicationException;

import java.text.DecimalFormat;
import java.util.Collection;
import java.util.HashSet;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticalHeuristicSearch extends AutomaticProver {

    private final String proverName ="tactical_heuristic";

    public TacticalHeuristicSearch() {super(new NoStrategy());}

    public TacticalHeuristicSearch(Strategy strategy) {
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
        Set<ProofAttempt> closed = new HashSet<>();
        // the list of proof attempts, which still have to be visited
        PriorityQueue<ProofAttempt> attempts = new PriorityQueue<>();
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
            // create tactic applications
            Set<PossibleTacticApplication> tacticApplications = AutomaticUtils.createAllPossibleTacticApplications(subgoalindex);
            for (PossibleTacticApplication app : tacticApplications) {
                ProofTrace newCurrent = new ProofTrace(currentProof.getGoals(), currentProof.getInferenceApplications());
                boolean hasBeenApplied = app.apply(newCurrent, getPrettyName());
                if (hasBeenApplied) {
                    ProofAttempt newAttempt = new ProofAttempt(newCurrent, getStrategy());
                    attempts.add(newAttempt);
                }
            }
            // create single rule applications
            SpiderDiagramOccurrence target = SpiderDiagramOccurrence.wrapDiagram(currentProof.getLastGoals().getGoalAt(subgoalindex), 0);
            Set<? extends PossibleRuleApplication<? extends RuleArg>> applications = AutomaticUtils.createAllPossibleRuleApplications(subgoalindex, target, contours);
            // apply all possible rules to the current proof, creating a new proof for each application
            for(PossibleRuleApplication nextRule : applications) {
                ProofTrace newCurrent = new ProofTrace(currentProof.getGoals(), currentProof.getInferenceApplications());
                boolean superfl = nextRule.isSuperfluous(newCurrent);
                if (superfl) numOfSuperFl++;
                boolean hasBeenApplied =  !superfl  && nextRule.apply(newCurrent, getPrettyName());
                if (hasBeenApplied) {
                    // save the new proof within the set of not yet considered proofs
                    ProofAttempt newAttempt = new ProofAttempt(newCurrent, getStrategy());
                    attempts.add(newAttempt);
                }
            }
            closed.add(currentAttempt);
        }
        // TODO: remove sysout
        printStatistics(closed, attempts,startTime,numOfSuperFl);
        return null;
    }

    private void printStatistics(Set<ProofAttempt> closed, PriorityQueue<ProofAttempt> attempts, long startTime, long superfluousAttemps) {
        long duration = System.nanoTime() - startTime;
        DecimalFormat format = new DecimalFormat("###,###,###,###");
        String fullNumber= format.format(closed.size()+attempts.size());
        String considered = format.format(closed.size());
        String superfluous = format.format(superfluousAttemps);
        System.out.println("Prover: "+getPrettyName());
        System.out.println("Considered proof attempts: "+considered);
        System.out.println("Complete number of created proofs: "+fullNumber);
        System.out.println("Number of prevented rule applications: "+superfluous);
        System.out.println("Time needed: "+ TimeUnit.NANOSECONDS.toMillis(duration)+"ms ("+ TimeUnit.NANOSECONDS.toSeconds(duration)+"s)" );
        System.out.println("Average per Attempt: " + TimeUnit.NANOSECONDS.toMillis(duration)/closed.size() +"ms\n");
    }

    @Override
    public AutomaticProver getAutomaticProver() {
        return this ;
    }

    @Override
    public String getAutomaticProverName() {
        return proverName;
    }

    @Override
    public String getDescription() {
        return "A* search using single rules and tactics using the selected strategy";
    }

    @Override
    public String getPrettyName() {
        return "Tactical A* Search";
    }
}
