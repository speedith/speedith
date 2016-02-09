package speedith.core.reasoning.automatic;


/**
 * Created by sl542 on 13/11/15.
 */
public class AutomaticProofException extends Exception {


    private static final long serialVersionUID = 8849081025268462570L;

    /**
     * Creates a new instance of <code>RuleApplicationException</code> without detail message.
     */
    public AutomaticProofException() {
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public AutomaticProofException(String msg) {
        super(msg);
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified detail message.
     * @param msg the detail message.
     * @param cause
     */
    public AutomaticProofException(String msg, Throwable cause) {
        super(msg, cause);
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified detail message.
     * @param cause
     */
    public AutomaticProofException(Throwable cause) {
        super(cause);
    }
}


