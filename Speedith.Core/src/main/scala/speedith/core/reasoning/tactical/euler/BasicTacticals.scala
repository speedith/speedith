package speedith.core.reasoning.tactical.euler

import speedith.core.lang.NullSpiderDiagram
import speedith.core.reasoning.args.SubgoalIndexArg
import speedith.core.reasoning.{Goals, Proof}
import speedith.core.reasoning.tactical.{TacticApplicationResult, TacticApplicationException}

import scala.reflect.internal.util.Collections


/**
 * Basic tacticals to combine other tacticals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object BasicTacticals {

  val emptyGoals =  Goals.createGoalsFrom(NullSpiderDiagram.getInstance())

  def THEN(tac1: Tactical, tac2: Tactical) = (name:String) => (state : Goals) => (subgoalIndex:Int) => (result : TacticApplicationResult) =>{
    tac1(name)(state)(subgoalIndex)(result) flatMap (res => tac2(name)(res.getGoals)(subgoalIndex)(res))
  }

  def ORELSE(tac1 : Tactical, tac2 : Tactical) : Tactical = (name:String) => (state : Goals) =>(subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    val state1 = tac1(name)(state)(subGoalIndex)(result)
    if (state1.isEmpty) {
      tac2(name)(state)(subGoalIndex)(result)
    } else {
      state1
    }
  }

  def id:Tactical = (name:String) => (state:Goals) =>(subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    Some(new TacticApplicationResult(result.getApplicationList, state))
  }

  def fail:Tactical = (name:String) =>(state:Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    None
  }

  def TRY(tac : Tactical) = (name:String) => (state:Goals) =>(subGoalIndex:Int)=>(result : TacticApplicationResult) => {
    ORELSE(tac, id)(name)(state)(subGoalIndex)(result)
  }

  def REPEAT(tac : Tactical): Tactical = (name:String) =>(state : Goals) => (subGoalIndex:Int) =>(result : TacticApplicationResult) =>{
    ORELSE(THEN(tac, REPEAT(tac)), id )(name)(state)(subGoalIndex)(result)
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
