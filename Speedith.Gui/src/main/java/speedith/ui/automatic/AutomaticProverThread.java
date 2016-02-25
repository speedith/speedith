package speedith.ui.automatic;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.automatic.AutomaticProofException;
import speedith.core.reasoning.automatic.AutomaticProver;

import javax.swing.*;
import java.util.concurrent.Callable;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AutomaticProverThread extends SwingWorker<Proof, Object> {

    private Proof proof;

    private AutomaticProver prover;

    private boolean finished;

    public AutomaticProverThread(Proof proofToExtend, AutomaticProver prover) {
        this.proof = proofToExtend;
        this.prover = prover;
        finished = false;
    }



    public void setProof(Proof proof) {
        this.proof = proof;
    }

    public boolean isFinished() {
        return finished;
    }

    @Override
    protected Proof doInBackground() throws Exception {
        Proof newProof = null;
        newProof = prover.extendProof(proof);
        proof = newProof;
        finished = true;
        return newProof;
    }
}
