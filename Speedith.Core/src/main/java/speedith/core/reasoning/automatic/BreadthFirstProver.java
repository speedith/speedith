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
import speedith.core.reasoning.tactical.TacticApplicationException;

import java.text.DecimalFormat;
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
    protected Proof prove(Proof p, int subgoalindex) throws RuleApplicationException, TacticApplicationException, AutomaticProofException {
        p = tryToFinish(p, subgoalindex);
        if (p.isFinished()) {
            return p;
        }
        // initialise the set of proofs to be considered
        List<Proof> currentProofs = new LinkedList<>();
        // we keep the set of closed proofs for statistics
        Set<Proof> closed = new HashSet<>();
        currentProofs.add( p);

         Goals currentGoals = p.getLastGoals();
        // get all names of contours present in the goals. This bounds the
        // possible proof rule applications, since contours not in this set
        // never have to be copied or introduced.
        Collection<String> contours = new HashSet<>();
        for (SpiderDiagram sd : currentGoals.getGoals()) {
            contours.addAll( AutomaticUtils.collectContours(sd));
        }
        Proof finishedProof = null;
        long numOfSuperFl = 0;
        long startTime= System.nanoTime();
        while (!Thread.currentThread().isInterrupted() && finishedProof == null && !currentProofs.isEmpty()) {
            Proof current = currentProofs.remove(0);
            current = tryToFinish(current, subgoalindex);
            if (current.isFinished()) {
                // we found a finished proof
                finishedProof = current;
            } else {
                // create all possible proof rules for this unfinished proof
                SpiderDiagramOccurrence target = SpiderDiagramOccurrence.wrapDiagram(current.getLastGoals().getGoalAt(subgoalindex), 0);
                Set<? extends PossibleRuleApplication<? extends RuleArg>> applications = AutomaticUtils.createAllPossibleRuleApplications(subgoalindex,target, contours);
                // apply all possible rules to the current proof, creating a new proof for each application
                for (PossibleRuleApplication nextRule : applications) {
                    ProofTrace newCurrent = new ProofTrace(current.getGoals(), current.getInferenceApplications());
                    boolean superfl = nextRule.isSuperfluous(newCurrent);
                    if (superfl) numOfSuperFl++;
                    boolean hasbeenApplied = !superfl && nextRule.apply(newCurrent, getPrettyName());
                    if (hasbeenApplied) {
                        // save the new proof within the set of not yet considered proofs
                        currentProofs.add(newCurrent);
                    }
                }
                closed.add(current);
            }
        }
        Set<Proof> attempts = new HashSet<>();
        attempts.addAll(closed);
        attempts.addAll(currentProofs);
        // TODO remove statistics
        printStatistics(closed, attempts, startTime, numOfSuperFl);
        return finishedProof;
    }

    private void printStatistics(Collection<Proof> closed, Collection<Proof> attempts, long startTime, long superfluousAttemps) {
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
