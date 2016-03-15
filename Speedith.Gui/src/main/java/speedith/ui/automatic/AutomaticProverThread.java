package speedith.ui.automatic;

import speedith.core.lang.TransformationException;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.automatic.AutomaticProver;

import javax.swing.*;
import java.util.concurrent.ExecutionException;

/**
 * Thread that tries to finish the given {@link Proof proof object} with
 * the given {@link AutomaticProver prover}.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AutomaticProverThread extends SwingWorker<Proof, Object> {

    /**
     * The name of the preference for activating automated search in the background
     */
    public static final String background_preference = "background_search";

    private Proof proof;

    private final AutomaticProver prover;

    private boolean finished;

    /**
     * Creates a new instance of this thread to extend the given proof
     * by the given prover object.
     *
     * @param proofToExtend The proof that will be extended to a finished proof if possible
     * @param prover        The proof method to be used
     */
    public AutomaticProverThread(Proof proofToExtend, AutomaticProver prover) {
        this.proof = proofToExtend;
        this.prover = prover;
        finished = false;
    }


    /**
     * Returns true if the prover was able to finish the proof
     *
     * @return true, if the proof could be finished
     */
    public boolean isFinished() {
        return finished;
    }

    @Override
    protected Proof doInBackground() throws Exception {
        Proof newProof;
        newProof = prover.extendProof(proof);
        proof = newProof;
        finished = (proof != null) && proof.getLastGoals().isEmpty();
        return newProof;
    }



    protected void setProof(Proof newProof){
            proof = newProof;
        }

    public Proof getProof() {
        return proof;
    }

}