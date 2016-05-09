package speedith.core.reasoning.tactical;

import speedith.core.reasoning.InferenceProvider;
import speedith.core.reasoning.args.SubgoalIndexArg;

import java.util.Locale;

/**
 * Common functionality of tactic objects.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public abstract class SimpleInferenceTactic implements InferenceTactic<SubgoalIndexArg>, TacticProvider {

    // <editor-fold defaultstate="collapsed" desc="InferenceProvider Implementation">
    @Override
    public String getDescription() {
        return getDescription(Locale.getDefault());
    }

    @Override
    public String getPrettyName() {
        return getPrettyName(Locale.getDefault());
    }

    @Override
    public String toString() {
        return getPrettyName();
    }
// </editor-fold>

    public InferenceProvider<SubgoalIndexArg> getProvider() {
        return this;
    }

    @Override
    public Class<SubgoalIndexArg> getArgumentType() {
        return SubgoalIndexArg.class;
    }

    @Override
    public InferenceTactic<SubgoalIndexArg> getTactic() {
        return this;
    }
}
