package speedith.core.reasoning.rules;

import speedith.core.i18n.Translations;
import speedith.core.lang.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * Removes the subgoal, if it consists of an implication, where premiss and conclusion are equal.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TrivialImplicationTautology extends SimpleInferenceRule<SubDiagramIndexArg> implements BasicInferenceRule<SubDiagramIndexArg>, ForwardRule<SubDiagramIndexArg>, Serializable{

    /**
     * The name of this inference rule. <p>This value is returned by the {@link TrivialImplicationTautology#getInferenceName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "trivial_implication_tautology";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = -5152228212901382731L;


    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        // Check that the arguments to this rule are of the correct type.
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        // This rule does not change the number of goals (it simply rewrites
        // sub-formulae to null diagrams).
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        // Now apply the rewrite on the chosen subgoal.
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new IdempotencyTransformer(arg), false);
        // Finally return the changed goals.
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }

    @Override
    public TrivialImplicationTautology getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return "Removes the diagram if it is of the form D -> D";
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    public String getPrettyName(Locale locale) {
        return "Trivial Implication Tautology";
    }

    @Override
    public Class<SubDiagramIndexArg> getArgumentType() {
        return SubDiagramIndexArg.class;
    }

    @Override
    public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
        return SingletonContainer.Instruction;
    }

    private static final class SingletonContainer {
        private static final SelectSingleOperatorInstruction Instruction = new SelectSingleOperatorInstruction(Operator.Implication, Operator.Equivalence);
    }

    private class IdempotencyTransformer extends IdTransformer {

        private final SubDiagramIndexArg arg;

        public IdempotencyTransformer(SubDiagramIndexArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target sub-diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // The compound diagram must be an implication:
                if (Operator.Implication.equals(csd.getOperator())) {
                    if (csd.getOperand(0).equals(csd.getOperand(1))) {
                        return SpiderDiagrams.createNullSD();
                    } else {
                        throw new TransformationException(i18n("RULE_IMPLICATION_TAUTOLOGY_NOT_APPLICABLE_SEM"));
                    }
                } else {
                    throw new TransformationException(i18n("RULE_IMPLICATION_TAUTOLOGY_NOT_APPLICABLE"));
                }
            }
            return null;
        }
    }

}
