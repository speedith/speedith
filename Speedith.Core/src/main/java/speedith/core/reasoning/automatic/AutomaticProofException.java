package speedith.core.reasoning.automatic;


/**
 * Thrown if an error occurrs during the execution of an automated proof method.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AutomaticProofException extends Exception {


    private static final long serialVersionUID = 8849081025268462570L;

    /**
     * Creates a new instance of <code>AutomaticProofException</code> without detail message.
     */
    public AutomaticProofException() {
    }

    /**
     * Constructs an instance of <code>AutomaticProofException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public AutomaticProofException(String msg) {
        super(msg);
    }

    /**
     * Constructs an instance of <code>AutomaticProofException</code> with the specified detail message and
     * original cause of the exception.
     * @param msg the detail message.
     * @param cause the initial cause
     */
    public AutomaticProofException(String msg, Throwable cause) {
        super(msg, cause);
    }

    /**
     * Constructs an instance of <code>AutomaticProofException</code> with the specified initial cause
     * of the exception.
     * @param cause the initial cause
     */
    public AutomaticProofException(Throwable cause) {
        super(cause);
    }
}


