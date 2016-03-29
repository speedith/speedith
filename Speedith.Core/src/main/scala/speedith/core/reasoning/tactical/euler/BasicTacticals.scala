package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.args.SubgoalIndexArg
import speedith.core.reasoning.{Goals, Proof}
import speedith.core.reasoning.tactical.{TacticApplicationResult, TacticApplicationException}


/**
 * Basic tacticals to combine other tacticals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object BasicTacticals {
  def THEN(tac1: Tactical, tac2: Tactical) = (name:String) => (state : Goals) => (subgoalIndex:Int) => (result : TacticApplicationResult) =>{
    val res = tac1(name)(state)(subgoalIndex)(result)
    tac2(name)(res.getLastGoal)(subgoalIndex)(res)
  }

  def ORELSE(tac1 : Tactical, tac2 : Tactical) : Tactical = (name:String) => (state : Goals) =>(subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    val state1 = tac1(name)(state)(subGoalIndex)(result)
    if (state1.equals(result)) {
      tac2(name)(state)(subGoalIndex)(result)
    } else {
      state1
    }
  }

  def id:Tactical = (name:String) => (state:Goals) =>(subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    result
  }

  def fail:Tactical = (name:String) =>(state:Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    new TacticApplicationResult()
  }

  def TRY(tac : Tactical) = (name:String) => (state:Goals) =>(subGoalIndex:Int)=>(result : TacticApplicationResult) => {
    ORELSE(tac, id)(name)(state)(subGoalIndex)(result)
  }

  def REPEAT(tac : Tactical): Tactical = {//(name:String) =>(state : Goals) => (subGoalIndex:Int) =>(result : TacticApplicationResult) =>{
    ORELSE(THEN(tac, REPEAT(tac)), id )//(name)(state)(subGoalIndex)(result)
  }

  def DEPTH_FIRST (predicate:Goals => Boolean, tac:Tactical):Tactical =  (name:String) => (state :Goals) =>(subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    if (predicate(state)) {
      id(name)(state)(subGoalIndex)(result)
    } else {
      THEN(tac, DEPTH_FIRST(predicate, tac))(name)(state)(subGoalIndex)(result )
    }
  }

  @throws(classOf[TacticApplicationException])
  def BY( tac : Tactical) = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result : TacticApplicationResult) => {
      tac(name)(state)(subGoalIndex)(result)
  }

}
