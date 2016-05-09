package speedith.core.reasoning.tactical;

import speedith.core.reasoning.InferenceProvider;
import speedith.core.reasoning.args.SubgoalIndexArg;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface TacticProvider extends InferenceProvider<SubgoalIndexArg> {

    Tactic<SubgoalIndexArg> getTactic();

    boolean isHighLevel();
}
