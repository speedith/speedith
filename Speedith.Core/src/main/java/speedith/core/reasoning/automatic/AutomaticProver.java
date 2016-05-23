package speedith.core.reasoning.automatic;

import speedith.core.lang.TransformationException;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.CompoundSpiderDiagramOccurrence;
import speedith.core.reasoning.automatic.wrappers.PrimarySpiderDiagramOccurrence;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence;
import speedith.core.reasoning.rules.TrivialImplicationTautology;
import speedith.core.reasoning.rules.util.ReasoningUtils;
import speedith.core.reasoning.tactical.TacticApplicationException;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class AutomaticProver  implements  AutomaticProof, AutomaticProverProvider {

    private Strategy strategy;

    public AutomaticProver(Strategy strategy) {
        this.strategy = strategy;
    }

    public Strategy getStrategy() {
        return strategy;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Creates a {@link Proof} object for the given set of initial goals using the {@link Strategy}.
     *
     * @param initialGoals The set of SpiderDiagrams for which a proof will be constructed
     * @return the constructed Proof object
     * @throws AutomaticProofException if no Proof could be constructed
     */
    public Proof generateProof(Goals initialGoals) throws AutomaticProofException {
        // currently only Spider Diagrams which have an implication as their major operator
        // and where the assumption and conclusion are conjunctive diagrams
        // can be proved
        if (!ReasoningUtils.isImplicationOfConjunctions(initialGoals.getGoalAt(0))) {
            throw new AutomaticProofException("The current goal is not an implication of conjunctions.");
        }

        // workaround as long as Speedith doesn't support several subgoals at once
        int subGoalToProve = 0;

        // introduce all zones that are only implicit in the
        // data structure. I.e. present_zones returns the zone set in
        // the usual sense of spider diagrams
        Proof init = new ProofTrace(ReasoningUtils.normalize(initialGoals));
        //AppliedRules appliedRules = new AppliedRules();

        Proof result;
        try {
            result = prove(init, subGoalToProve);
        } catch (RuleApplicationException|TacticApplicationException e) {
            throw new AutomaticProofException("Unable to prove current goal because of an illegal rule application",e);
        }
        if (result == null || !result.isFinished()) {
            throw  new AutomaticProofException("Unable to prove current goal");
        }
        return result;
    }

    @Override
    public Proof extendProof(Proof proof) throws AutomaticProofException {
        // workaround as long as Speedith doesn't support several subgoals at once
        int subGoalToProve = 0;
        if (proof.isFinished()) {
            System.out.println("Proof already finished");
            return proof;
//            throw new AutomaticProofException("The proof is already finished");
        }
        if (!ReasoningUtils.isImplicationOfConjunctions(proof.getLastGoals().getGoalAt(subGoalToProve))) {
            throw new AutomaticProofException("The current goal is not an implication of conjunctions");
        }
        // proof generators can only be applied to normalised spider diagrams
        Goals normalised = ReasoningUtils.normalize(proof.getLastGoals());
        if (!normalised.equals(proof.getLastGoals())) {
            throw  new AutomaticProofException("The current goal is not normalised!");
        }
        // create a new proof object, so that we do not mess with the supplied proof
        Proof initial = new ProofTrace(proof.getGoals(), proof.getInferenceApplications());

        Proof result;
        try {
            result = prove(initial, subGoalToProve);
        } catch (RuleApplicationException|TacticApplicationException e) {
            throw new AutomaticProofException("Unable to prove current goal because of an illegal rule application",e);
        }
        if (!Thread.currentThread().isInterrupted() && (result == null || !result.isFinished())) {
            throw  new AutomaticProofException("Unable to prove current goal");
        }
        return result;

    }

    protected abstract Proof prove (Proof p, int subgoalindex) throws RuleApplicationException, TacticApplicationException, AutomaticProofException;


    /**
     * Tries to finish up the given Proof p by applying ImplicationTautology to
     * the given subgoal in the last goals in the proof.
     * @param p The proof that will be finished
     * @param subGoalIndex The subgoal that will be finished
     * @return If ImplicationTautology was applied: the finished proof, otherwise the proof p
     * @throws RuleApplicationException
     */
    protected Proof tryToFinish(Proof p, int subGoalIndex) throws  RuleApplicationException, TacticApplicationException{
        if (p.isFinished()) return p;
        TrivialImplicationTautology tautology = new TrivialImplicationTautology();
        SubDiagramIndexArg index = new SubDiagramIndexArg(subGoalIndex,0);
        try {
            p.applyRule(tautology, index, RuleApplicationType.AUTOMATIC, getPrettyName());
        } catch (TransformationException e) {
            // TrivialImplicationTautology throws a TransformationException, if the rule
            // could not be applied (i.e., if the syntactic equivalence could not
            // be established). I abuse this behaviour by silently swallowing
            // the exception, Hence, if such an exception is thrown, the old proof
            // will be returned.
        }
        return p;
    }



    /*
     * Prints all subdiagrams of the given SpiderDiagramOccurrence to the console including
     * their occurrences in the SpiderDiagramOccurrence.
     */
    public static void printSubDiagramIndices(SpiderDiagramOccurrence current) {
        if (current instanceof PrimarySpiderDiagramOccurrence) {
            System.out.println( current.getOccurrenceIndex() + ":  "+current.getDiagram());
        } else {
            CompoundSpiderDiagramOccurrence cs = (CompoundSpiderDiagramOccurrence) current;
            System.out.println( current.getOccurrenceIndex() + ":  "+current.getDiagram());
            for (SpiderDiagramOccurrence sub: cs.getOperands()) {
                printSubDiagramIndices(sub);
            }

        }

    }
}
