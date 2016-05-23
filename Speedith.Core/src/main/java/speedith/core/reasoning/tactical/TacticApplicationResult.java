package speedith.core.reasoning.tactical;

import speedith.core.reasoning.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticApplicationResult implements InferenceApplicationResult, Serializable {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private List<InferenceApplication> applications;

    private Goals goals;

    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">

    public TacticApplicationResult() {
        this.applications = new ArrayList<>();
    }

    public  TacticApplicationResult(List<InferenceApplication> applications, Goals goals) {
        this.applications= applications;
        this.goals = goals;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the goals that have been the result of an {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * inference rule application}.
     * <p>May return {@code null}, which indicates that the application of the
     * inference rule yielded no subgoals. The same hold for an empty {@link Goals}
     * instance.</p>
     * @return the goals that have been the result of an {@link InferenceRule#apply(speedith.core.reasoning.args.RuleArg, speedith.core.reasoning.Goals)
     * inference rule application}.
     * <p>May return {@code null}, which indicates that the application of the
     * inference rule yielded no subgoals. The same hold for an empty {@link Goals}
     * instance.</p>
     */
    public List<InferenceApplication> getApplicationList() {
        return applications;
    }



    public Goals getGoals() {
        return goals;
    }
    //</editor-fold>

}
