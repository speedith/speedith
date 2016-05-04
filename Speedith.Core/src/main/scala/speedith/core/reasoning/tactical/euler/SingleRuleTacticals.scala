package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.{Goals, Proof}
import speedith.core.reasoning.tactical.{TacticApplicationResult, TacticApplicationException}
import speedith.core.reasoning.tactical.euler.Choosers._
import speedith.core.reasoning.tactical.euler.Predicates._
import speedith.core.reasoning.tactical.euler.BasicTacticals._

/**
 * Contains tacticals which can be applied to a proof. In contrast to the
  * elements of [[Tactics Tactics]], the tacticals can be applied
  * without adding any more predicates.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object SingleRuleTacticals {

  @throws(classOf[TacticApplicationException])
  def introduceContour: Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) =>  {
    BY(THEN(Tactics.introduceContour( _=>true, anyContour))(TRY(Tactics.trivialTautology)))(name)(state)(subGoalIndex)(result)
  }

  /*  @throws(classOf[TacticApplicationException])
  def introduceShadedZone: Tactical = (name:String) => (state:Goals)  =>  {
    BY(THEN(Tactics.introduceShadedZone(0,isPrimaryAndContainsMissingZones,someMissingZone),TRY(Tactics.trivialTautology(0))))(name)(state)
  }

  @throws(classOf[TacticApplicationException])
  def removeShadedZone: Tactical = (name:String) => (state:Goals)  =>  {
    BY(THEN(Tactics.removeShadedZone(0,someShadedZone), TRY(Tactics.trivialTautology(0))))(name)(state)
  }

  @throws(classOf[TacticApplicationException])
  def eraseContour: Tactical = (name:String) => (state:Goals)  =>  {
    BY(THEN(Tactics.eraseContour(0,containsContours,anyContour), TRY(Tactics.trivialTautology(0))))(name)(state)
  }
  */
  @throws(classOf[TacticApplicationException])
  def trivialTautology : Tactical = (name:String) => (state:Goals)  => (subGoalIndex : Int) => (result : TacticApplicationResult) => {
    BY(Tactics.trivialTautology)(name)(state)(subGoalIndex)(result)
  }


}
