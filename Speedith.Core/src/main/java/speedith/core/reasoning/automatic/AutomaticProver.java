package speedith.core.reasoning.automatic;

import speedith.core.lang.*;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofTrace;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.automatic.strategies.Strategy;
import speedith.core.reasoning.automatic.wrappers.CompoundSpiderDiagramWrapper;
import speedith.core.reasoning.automatic.wrappers.PrimarySpiderDiagramWrapper;
import speedith.core.reasoning.automatic.wrappers.SpiderDiagramWrapper;
import speedith.core.reasoning.rules.ImplicationTautology;
import speedith.core.reasoning.rules.TrivialImplicationTautology;
import speedith.core.reasoning.rules.util.AutomaticUtils;
import speedith.core.reasoning.rules.util.ReasoningUtils;

import java.util.ArrayList;

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
        } catch (RuleApplicationException e) {
            AutomaticProofException exc = new AutomaticProofException("Unable to prove current goal because of an illegal rule application");
            exc.initCause(e);
            e.printStackTrace();  //TODO: for debugging. Remove if not needed anymore
            throw exc;
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
        if (!ReasoningUtils.isImplicationOfConjunctions(proof.getLastGoals().getGoalAt(subGoalToProve))) {
            throw new AutomaticProofException("The current goal is not an implication of conjunctions");
        }
        // proof generators can only be applied to normalised spider diagrams
        Goals normalised = ReasoningUtils.normalize(proof.getLastGoals());
        if (!normalised.equals(proof.getLastGoals())) {
            throw  new AutomaticProofException("The current goal is not normalised!");
        }
        // create a new proof object, so that we do not mess with the supplied proof
        Proof initial = new ProofTrace(proof.getGoals(), proof.getRuleApplications());

        Proof result;
        try {
            result = prove(initial, subGoalToProve);
        } catch (RuleApplicationException e) {
            AutomaticProofException exc = new AutomaticProofException("Unable to prove current goal because of an illegal rule application");
            exc.initCause(e);
            e.printStackTrace();  //TODO: for debugging. Remove if not needed anymore
            throw exc;
        }
        if (result == null || !result.isFinished()) {
            throw  new AutomaticProofException("Unable to prove current goal");
        }
        return result;

    }

    protected abstract Proof prove (Proof p, int subgoalindex) throws RuleApplicationException, AutomaticProofException;


    /**
     * Tries to finish up the given Proof p by applying ImplicationTautology to
     * the given subgoal in the last goals in the proof.
     * @param p The proof that will be finished
     * @param subGoalIndex The subgoal that will be finished
     * @return If ImplicationTautology was applied: the finished proof, otherwise the proof p
     * @throws RuleApplicationException
     */
    protected Proof tryToFinish(Proof p, int subGoalIndex) throws  RuleApplicationException{
        TrivialImplicationTautology tautology = new TrivialImplicationTautology();
        SubDiagramIndexArg index = new SubDiagramIndexArg(subGoalIndex,0);
        try {
            p.applyRule(tautology, index);
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
    * Creates a SpiderDiagramWrapper for the given SpiderDiagram sd to reliably
    * refer to the different occurrences of diagrams in sd
    */
    public static SpiderDiagramWrapper wrapDiagram (SpiderDiagram sd, final int occurrenceIndex) {
        if (sd instanceof PrimarySpiderDiagram) {
            return new PrimarySpiderDiagramWrapper(sd, occurrenceIndex);
        }
        if (sd instanceof CompoundSpiderDiagram) {
            int newIndex = occurrenceIndex+1;
            ArrayList<SpiderDiagramWrapper> operands = new ArrayList<>();
            for(SpiderDiagram op: ((CompoundSpiderDiagram) sd).getOperands()) {
                SpiderDiagramWrapper opWrap = wrapDiagram(op, newIndex);
                operands.add(opWrap);
                newIndex+= opWrap.getDiagram().getSubDiagramCount();
            }
            return new CompoundSpiderDiagramWrapper(sd, occurrenceIndex, operands);

        }
        return null;
    }

    /*
     * Prints all subdiagrams of the given SpiderDiagramWrapper to the console including
     * their occurrences in the SpiderDiagramWrapper.
     */
    public static void printSubDiagramIndices(SpiderDiagramWrapper current) {
        if (current instanceof PrimarySpiderDiagramWrapper) {
            System.out.println( current.getOccurrenceIndex() + ":  "+current.getDiagram());
        } else {
            CompoundSpiderDiagramWrapper cs = (CompoundSpiderDiagramWrapper) current;
            System.out.println( current.getOccurrenceIndex() + ":  "+current.getDiagram());
            for (SpiderDiagramWrapper sub: cs.getOperands()) {
                printSubDiagramIndices(sub);
            }

        }

    }
}
