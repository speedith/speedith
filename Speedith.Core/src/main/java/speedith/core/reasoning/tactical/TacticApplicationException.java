package speedith.core.reasoning.tactical;

/**
 * Thrown if a tactic could not be applied.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticApplicationException extends Exception {
    private static final long serialVersionUID = -2202142575161820257L;

    public TacticApplicationException(String s) {
        super(s);
    }
}
