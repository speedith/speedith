package speedith.core.reasoning;

/**
 * Contains the result of successfully applying an inference
 * to a proof.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface InferenceApplicationResult {

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the goals that have been the result of an {@link Inference#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * inference application}.
     * <p>May return {@code null}, which indicates that the application of the
     * inference yielded no subgoals. The same hold for an empty {@link Goals}
     * instance.</p>
     * @return the goals that have been the result of an {@link Inference#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * inference rule application}.
     * <p>May return {@code null}, which indicates that the application of the
     * inference yielded no subgoals. The same hold for an empty {@link Goals}
     * instance.</p>
     */
     Goals getGoals();
    //</editor-fold>
}
