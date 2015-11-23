package speedith.core.reasoning.rules;

import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.ZoneArg;
import speedith.core.reasoning.rules.instructions.SelectSingleZoneInstruction;
import speedith.core.reasoning.rules.transformers.RemoveShadedZoneTransformer;

import java.util.Locale;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class RemoveShadedZone extends SimpleInferenceRule<ZoneArg>
implements BasicInferenceRule<ZoneArg>, ForwardRule<ZoneArg> {

    public static final String InferenceRuleName = "Remove Shaded Zone";

    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }

    @Override
    public RuleApplicationResult apply(RuleArg args, Goals goals) throws RuleApplicationException {
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        ZoneArg subgoal = (ZoneArg) args;
        SpiderDiagram targetSubgoal = getSubgoal(subgoal, goals);
        newSubgoals[subgoal.getSubgoalIndex()] = targetSubgoal.transform(new RemoveShadedZoneTransformer(subgoal));
        return createRuleApplicationResult(newSubgoals);
    }

    @Override
    public InferenceRule<ZoneArg> getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceRuleName() {
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
    public Class<ZoneArg> getArgumentType() {
        return  ZoneArg.class;
    }

    @Override
    public RuleApplicationInstruction<ZoneArg> getInstructions() {
        return  new SelectSingleZoneInstruction();
    }
}
