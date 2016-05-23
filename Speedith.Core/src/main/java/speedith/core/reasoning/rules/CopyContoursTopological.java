package speedith.core.reasoning.rules;

import speedith.core.i18n.Translations;
import speedith.core.lang.DiagramType;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.ContourArg;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.rules.instructions.SelectContoursInstruction;
import speedith.core.reasoning.rules.transformers.CopyContoursTopologicalTransformer;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class CopyContoursTopological extends SimpleInferenceRule<MultipleRuleArgs> implements Serializable, ForwardRule<MultipleRuleArgs> {

        /**
         * The name of this inference rule.
         */
        public static final String InferenceRuleName = "copy_contours_topological";

        private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = 1065391918870981170L;


    @Override
        public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
            return apply(getContourArgsFrom(args), goals);
        }

        @Override
        public InferenceRule<MultipleRuleArgs> getInferenceRule() {
            return this;
        }

        @Override
        public String getInferenceName() {
            return InferenceRuleName;
        }

        @Override
        public String getDescription(Locale locale) {
            return Translations.i18n(locale, "COPY_CONTOURS_TOPOLOGICAL_DESCRIPTION");
        }

        @Override
        public String getCategory(Locale locale) {
            return Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS");
        }

        @Override
        public String getPrettyName(Locale locale) {
            return Translations.i18n(locale, "COPY_CONTOURS_TOPOLOGICAL_PRETTY_NAME");
        }

        @Override
        public Class<MultipleRuleArgs> getArgumentType() {
            return MultipleRuleArgs.class;
        }

        @Override
        public Set<DiagramType> getApplicableTypes() {
            return applicableTypes;
        }

        @Override
        public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
            return new SelectContoursInstruction();
        }

        private ArrayList<ContourArg> getContourArgsFrom(RuleArg args) throws RuleApplicationException {
            MultipleRuleArgs multipleRuleArgs = getTypedRuleArgs(args);
            MultipleRuleArgs.assertArgumentsNotEmpty(multipleRuleArgs);
            return ContourArg.getContourArgsFrom(multipleRuleArgs);
        }

    private RuleApplicationResult apply(ArrayList<ContourArg> targetContours, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        ContourArg inferenceTarget = targetContours.get(0);
        SpiderDiagram targetSubgoal = getSubgoal(inferenceTarget, goals);
        int indexOfParent = targetSubgoal.getParentIndexOf(inferenceTarget.getSubDiagramIndex());
        newSubgoals[inferenceTarget.getSubgoalIndex()] = targetSubgoal.transform(new CopyContoursTopologicalTransformer(indexOfParent, targetContours));
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }
}
