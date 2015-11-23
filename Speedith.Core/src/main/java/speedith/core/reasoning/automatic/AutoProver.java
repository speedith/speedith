package speedith.core.reasoning.automatic;

import speedith.core.lang.*;
import speedith.core.lang.util.CompoundDiagramsUtils;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.SpiderArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.*;
import speedith.core.reasoning.rules.util.AutomaticUtils;

import java.util.Collection;
import java.util.HashSet;

/**
 * Generates proofs for given subgoals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 * Created by sl542 on 11/11/15.
 *
 */
public class AutoProver {

    /**
     * Creates a proof without possibilities to set the wanted
     * heuristics.
     * @param initialGoals the Euler Diagram to prove. Has to be an implication,
     *                     where both the premise and the conclusion are purely conjunctive
     *                     diagrams.
     *
     * @return a proof of the goals
     */
    public static Proof generateProof(Goals initialGoals) throws AutomaticProofException {
       // currently only Spider Diagrams which have an imolication as their major operator
        // and where the assumption and conclusion are conjunctive diagrams
        // can be proved
        if (!isImplicationOfConjunctions(initialGoals.getGoalAt(0))) {
            throw new AutomaticProofException("The current goal is not an implication of conjunctions.");
        }

        printSubDiagramIndices(initialGoals.getGoalAt(0), initialGoals.getGoalAt(0));

        Proof init = new ProofTrace(initialGoals);
        AppliedEquivalenceRules appliedRules = new AppliedEquivalenceRules();
        Proof result = null;
        try {
            result = prove(init, appliedRules);
        } catch (RuleApplicationException e) {
            AutomaticProofException exc = new AutomaticProofException("Unable to prove current goal because of an illegal rule application");
            exc.initCause(e);
            throw exc;
        }
        if (result == null || !result.isFinished()) {
            throw  new AutomaticProofException("Unable to prove current goal");
        }
        return result;
    }

    private static void printSubDiagramIndices(SpiderDiagram current, SpiderDiagram goalAt) {
        if (current instanceof PrimarySpiderDiagram) {
            System.out.println( goalAt.getSubDiagramIndex(current) + ":  "+current);
        } else {
            CompoundSpiderDiagram cs = (CompoundSpiderDiagram) current;
            System.out.println( goalAt.getSubDiagramIndex(current) + ":  "+current);
            for (SpiderDiagram sub: cs.getOperands()) {
                printSubDiagramIndices(sub, goalAt);
            }

        }

    }

    private static Proof prove(Proof p, AppliedEquivalenceRules appliedRules) throws RuleApplicationException {
        p = tryToFinish(p);
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
        SpiderDiagram target = currentGoals.getGoalAt(0);
        Collection<PossibleRuleApplication> applications = AutomaticUtils.createAllPossibleRuleApplications(target, contours, appliedRules);
        for (PossibleRuleApplication ruleApp : applications) {
            boolean hasbeenApplied = applyRule(ruleApp, p.getLastGoals().getGoalAt(0),p, appliedRules);
            if (hasbeenApplied) {
                p = prove(p, appliedRules);
                if (p.isFinished()) {
                    return p;
                }
                //FIXME: addition of copy contour creates some endless(?) recursion. Stackoverflow
                p.undoStep();
            }
        }

        return p;
    }

    private static Proof tryToFinish(Proof p) {
        ImplicationTautology tautology = new ImplicationTautology();
        Goals goalsAt = p.getLastGoals();
        SubDiagramIndexArg index = new SubDiagramIndexArg(0,0);
        try {
            p.applyRule(tautology,index);
        }catch (TransformationException e) {
            //throw e;
        } catch (RuleApplicationException e) {
            e.printStackTrace();
        }
        return p;
    }

    private static boolean applyRule(PossibleRuleApplication ruleApp, SpiderDiagram sd, Proof p, AppliedEquivalenceRules appliedRules) throws RuleApplicationException {
        if (ruleApp instanceof PossibleIntroduceContourApplication) {
            PossibleIntroduceContourApplication intro = (PossibleIntroduceContourApplication) ruleApp;
            String contour = intro.getContour();
            SpiderDiagram target = ruleApp.getTarget();
            if (!appliedRules.getIntroducedContours(target).contains(contour)) {
                p.applyRule(intro.getRule(), intro.getArg(0, sd));
                appliedRules.addIntroContour(target, contour);
                return true;
            }
        } else if (ruleApp instanceof PossibleConjunctionElimination) {
            PossibleConjunctionElimination pconjE = (PossibleConjunctionElimination) ruleApp;
            SpiderDiagram target = ruleApp.getTarget();
            p.applyRule(pconjE.getRule(), pconjE.getArg(0,sd));
            return true;
        } else if (ruleApp instanceof PossibleRemoveContourApplication) {
            PossibleRemoveContourApplication remove = (PossibleRemoveContourApplication) ruleApp;
            String contour = remove.getContour();
            SpiderDiagram target = ruleApp.getTarget();
            if (!appliedRules.getRemovedContours(target).contains(contour)) {
                p.applyRule(remove.getRule(), remove.getArg(0,sd));
                appliedRules.addRemoveContour(target, contour);
                return true;
            }
        } else if (ruleApp instanceof PossibleRemoveShadingApplication) {
            PossibleRemoveShadingApplication shading = (PossibleRemoveShadingApplication) ruleApp;
            Zone zone= shading.getZone();
            SpiderDiagram target = ruleApp.getTarget();
            if (!appliedRules.getRemovedShading(target).contains(zone)) {
                p.applyRule(shading.getRule(), shading.getArg(0,sd));
                appliedRules.addRemovedShading(target, zone);
                return true;
            }
        }  else if (ruleApp instanceof PossibleCopyContourApplication) {
            PossibleCopyContourApplication copy = (PossibleCopyContourApplication) ruleApp;
            String contour = copy.getContour();
            SpiderDiagram target = ruleApp.getTarget();
            if (!appliedRules.getCopiedContours(target).contains(contour)) {
                try {

                    p.applyRule(copy.getRule(), copy.getArg(0,sd));
                } catch (TransformationException e) {
                    e.printStackTrace();
                }
                appliedRules.addCopiedContour(sd, contour);
                return true;
            }
        }
        return false;

    }

    private static boolean isImplicationOfConjunctions(SpiderDiagram goal) {
        if (goal instanceof CompoundSpiderDiagram) {
            CompoundSpiderDiagram csd = (CompoundSpiderDiagram) goal;
            if (csd.getOperator().equals(Operator.Implication)) {
                SpiderDiagram premiss = csd.getOperand(0);
                SpiderDiagram conclusion = csd.getOperand(1);
                if (AutomaticUtils.isConjunctive(premiss) && AutomaticUtils.isConjunctive(conclusion)) {
                    return true;
                }
            }
        }
        return false;
    }



}
