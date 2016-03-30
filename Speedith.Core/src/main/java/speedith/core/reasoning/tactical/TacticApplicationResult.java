package speedith.core.reasoning.tactical;

import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceApplicationResult;
import speedith.core.reasoning.InferenceRule;
import speedith.core.reasoning.RuleApplicationResult;

import java.util.ArrayList;
import java.util.List;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticApplicationResult implements InferenceApplicationResult {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private List<RuleApplicationResult> applications;

    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises an instance of the RuleApplicationResult class.
     * @param ruleApplication the goals that remained after the application of an
     * inference rule.
     */
    public TacticApplicationResult(RuleApplicationResult ruleApplication) {
        this.applications = new ArrayList<>();
        this.applications.add(ruleApplication);
    }

    public TacticApplicationResult() {
        this.applications = new ArrayList<>();
    }

    public  TacticApplicationResult(List<RuleApplicationResult> applications) {
        this.applications = applications;
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
    public List<RuleApplicationResult> getApplicationList() {
        return applications;
    }



    public Goals getGoals() {
        return applications.size() > 0 ? applications.get(applications.size() -1).getGoals() : null;
    }
    //</editor-fold>

}
