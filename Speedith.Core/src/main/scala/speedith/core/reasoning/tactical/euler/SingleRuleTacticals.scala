package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import speedith.core.reasoning.tactical.TacticApplicationException
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
  def introduceContour(state:Proof)  =  {
    BY(THEN(Tactics.introduceContour(0),TRY(Tactics.trivialTautology(0))))(state)
  }

  @throws(classOf[TacticApplicationException])
  def introduceShadedZone(state:Proof) = {
    BY(THEN(Tactics.introduceShadedZone(0,isPrimaryAndContainsMissingZones,anyMissingZone),TRY(Tactics.trivialTautology(0))))(state)
  }

  @throws(classOf[TacticApplicationException])
  def removeShadedZone(state:Proof)= {
    BY(THEN(Tactics.removeShadedZone(0,anyShadedZone), TRY(Tactics.trivialTautology(0))))(state)
  }

  @throws(classOf[TacticApplicationException])
  def eraseContour(state:Proof)= {
    BY(THEN(Tactics.eraseContour(0,_ => true,anyContour), TRY(Tactics.trivialTautology(0))))(state)
  }

  @throws(classOf[TacticApplicationException])
  def trivialTautology (state:Proof)= {
    BY(Tactics.trivialTautology(0))(state)
  }


}
