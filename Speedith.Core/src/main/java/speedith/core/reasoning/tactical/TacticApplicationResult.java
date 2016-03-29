package speedith.core.reasoning.tactical;

import speedith.core.reasoning.Goals;
import speedith.core.reasoning.InferenceApplicationResult;
import speedith.core.reasoning.InferenceRule;

import java.util.ArrayList;
import java.util.List;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class TacticApplicationResult implements InferenceApplicationResult {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private List<Goals> goals;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises an instance of the RuleApplicationResult class.
     * @param goals the goals that remained after the application of an
     * inference rule.
     */
    public TacticApplicationResult(Goals goals) {
        this.goals = new ArrayList<>();
        this.goals.add(goals);
    }

    public TacticApplicationResult() {
        this.goals = new ArrayList<>();
    }

    public  TacticApplicationResult(List<Goals> goalList) {
        this.goals = goalList;
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
    public List<Goals> getGoalsList() {
        return goals;
    }

    public Goals getLastGoal() {
        return goals.get(goals.size() -1);
    }
    //</editor-fold>

}
