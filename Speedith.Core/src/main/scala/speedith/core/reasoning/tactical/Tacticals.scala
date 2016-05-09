package speedith.core.reasoning.tactical

import speedith.core.reasoning.Goals


/**
 * Basic tacticals to combine other tacticals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object Tacticals {

  def THEN: Tactic => Tactic => Tactic = (tac1: Tactic) => (tac2: Tactic) => (name: String) => (state: Goals) => (subgoalIndex: Int) => (result: TacticApplicationResult) => {
    tac1(name)(state)(subgoalIndex)(result) flatMap (res => tac2(name)(res.getGoals)(subgoalIndex)(res))
  }

  def ORELSE: Tactic => Tactic => Tactic =
    (tac1: Tactic) => (tac2: Tactic) => (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
      val state1 = tac1(name)(state)(subGoalIndex)(result)
      if (state1.isEmpty) {
        tac2(name)(state)(subGoalIndex)(result)
      } else {
        state1
      }
    }

  def id: Tactic = (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
    Some(new TacticApplicationResult(result.getApplicationList, state))
  }

  def fail: Tactic = (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
    None
  }

  def TRY: Tactic => Tactic = (tac : Tactic) =>  {
    ORELSE(tac)(id)
  }

  def REPEAT: Tactic => Tactic =
    (tac: Tactic) => (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
      ORELSE(THEN(tac)(REPEAT(tac)))(id)(name)(state)(subGoalIndex)(result)
    }

  def DEPTH_FIRST: (Goals => Int => Boolean) => Tactic => Tactic =
    (predicate: Goals => Int => Boolean) => (tac: Tactic) => (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
      if (predicate(state)(subGoalIndex)) {
        id(name)(state)(subGoalIndex)(result)
      } else {
        THEN(tac)(DEPTH_FIRST(predicate)(tac))(name)(state)(subGoalIndex)(result)
      }
    }

  def COND: (Goals => Int => Boolean) => Tactic => Tactic => Tactic =
    (p: Goals => Int => Boolean) => (tac1: Tactic) => (tac2: Tactic) => (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
      if (p(state)(subGoalIndex)) {
        tac1(name)(state)(subGoalIndex)(result)
      } else {
        tac2(name)(state)(subGoalIndex)(result)
      }
    }

  @throws(classOf[TacticApplicationException])
  def BY: Tactic => Tactic = (tac: Tactic) => (name: String) => (state: Goals) => (subGoalIndex: Int) => (result: TacticApplicationResult) => {
    tac(name)(state)(subGoalIndex)(result)
  }

}
