package speedith.core.reasoning.rules;

import com.sun.org.apache.xpath.internal.operations.Mult;
import speedith.core.lang.DiagramType;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.MultipleRuleArgs;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectSingleZoneInstruction;
import speedith.core.reasoning.rules.transformers.RemoveShadedZoneTransformer;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class RemoveShadedZone extends SimpleInferenceRule<MultipleRuleArgs>
implements BasicInferenceRule<MultipleRuleArgs>, ForwardRule<MultipleRuleArgs>, Serializable {

    public static final String InferenceRuleName = "Remove Shaded Zone";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
    private static final long serialVersionUID = 7113122453070471789L;

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }


    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        MultipleRuleArgs ruleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(ruleArgs);
        ArrayList<ZoneArg> zones = getZoneArgsFrom(ruleArgs);
        SubDiagramIndexArg target = getTargetDiagramArg(ruleArgs);
        return apply(target, zones, goals );
    }

    private RuleApplicationResult apply(SubDiagramIndexArg target, ArrayList<ZoneArg> targetContours, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        SpiderDiagram targetSubgoal = getSubgoal(target, goals);
        newSubgoals[target.getSubgoalIndex()] = targetSubgoal.transform(new RemoveShadedZoneTransformer(target, targetContours));
        return createRuleApplicationResult(newSubgoals);
    }

    public ArrayList<ZoneArg> getZoneArgsFrom(MultipleRuleArgs args) throws RuleApplicationException {
        MultipleRuleArgs multipleRuleArgs = getTypedRuleArgs(args);
        MultipleRuleArgs.assertArgumentsNotEmpty(multipleRuleArgs);
        ArrayList<ZoneArg> contourArgs = new ArrayList<>();
        int subDiagramIndex = -1;
        int goalIndex = -1;
        for (RuleArg ruleArg : multipleRuleArgs) {
            // an interactive application of IntroContour contains also a SubDiagramIndexArg,
            // to refer to the diagram the rule shall be applied to.
            if (ruleArg instanceof ZoneArg) {
                ZoneArg zoneArg = ZoneArg.getZoneArgFrom(ruleArg);
                subDiagramIndex = ZoneArg.assertSameSubDiagramIndices(subDiagramIndex, zoneArg);
                goalIndex = ZoneArg.assertSameGoalIndices(goalIndex, zoneArg);
                contourArgs.add(zoneArg);
            }
        }
        return contourArgs;
    }

    private SubDiagramIndexArg getTargetDiagramArg(MultipleRuleArgs args) throws RuleApplicationException {
        return (SubDiagramIndexArg) args.get(0);
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
        return "Removes a shaded zone from the set of visible zones.";
    }

    @Override
    public String getPrettyName(Locale locale) {
        return InferenceRuleName;
    }

    @Override
    public String getCategory(Locale locale) {
        return null;
    }

    @Override
    public Class<MultipleRuleArgs> getArgumentType() {
        return  MultipleRuleArgs.class;
    }

    @Override
    public RuleApplicationInstruction<MultipleRuleArgs> getInstructions() {
        return  new SelectSingleZoneInstruction();
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
