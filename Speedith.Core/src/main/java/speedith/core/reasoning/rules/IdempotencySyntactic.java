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
 * The implementation of the idempotency rule. It
 * can be applied to a CompoundSpiderDiagram and checks whether
 * the whole diagram can be replaced by one of its operands. This implementation checks for
 * exact syntactic equality of the operands.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class IdempotencySyntactic extends SimpleInferenceRule<SubDiagramIndexArg> implements BasicInferenceRule<SubDiagramIndexArg>, ForwardRule<SubDiagramIndexArg>, Serializable {


    /**
     * The name of this inference rule.
     * <p>This value is returned by the {@link Idempotency#getInferenceName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "idempotency_syntactic";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = 9106763180422196129L;

    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        SubDiagramIndexArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new IdempotencyTransformer(arg), false);
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public IdempotencySyntactic getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "IDEMPOTENCY_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return Translations.i18n(locale, "INF_RULE_CATEGORY_PURELY_SENTENTIAL");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return "Idempotency (Syntactic)";
    }

    @Override
    public Class<SubDiagramIndexArg> getArgumentType() {
        return SubDiagramIndexArg.class;
    }

    @Override
    public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
        // This rule needs a subdiagram. In fact, it needs an OR or AND operator
        return SingletonContainer.Instruction;
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }

    private static final class SingletonContainer {
        private static final SelectSingleOperatorInstruction Instruction = new SelectSingleOperatorInstruction(Operator.Conjunction, Operator.Disjunction);
    }

    private class IdempotencyTransformer extends IdTransformer {

        private final SubDiagramIndexArg arg;

        public IdempotencyTransformer(SubDiagramIndexArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // Is the compound diagram a conjunction or a disjunction?
                // Is it an implication or an equivalence?
                if (Operator.Conjunction.equals(csd.getOperator()) || Operator.Disjunction.equals(csd.getOperator())) {
                    if (csd.getOperand(0).equals(csd.getOperand(1))) {
                        return csd.getOperand(1);
                    }
                } else if (Operator.Equivalence.equals(csd.getOperator()) || Operator.Implication.equals(csd.getOperator())) {
                    if (csd.getOperand(0).equals(csd.getOperand(1))) {
                        return SpiderDiagrams.createNullSD();
                    }
                }
                throw new TransformationException(i18n("RULE_IDEMPOTENCY_NOT_APPLICABLE"));
            }
            return null;
        }
    }
}
