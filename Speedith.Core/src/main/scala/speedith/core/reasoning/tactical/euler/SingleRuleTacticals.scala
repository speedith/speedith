package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import speedith.core.reasoning.tactical.TacticApplicationException
import speedith.core.reasoning.tactical.euler.BasicTacticals._

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object SingleRuleTacticals {

  @throws(classOf[TacticApplicationException])
  def introduceContour(state:Proof)  =  {
    BY(Tactics.introduceContour(0,_),state)
  }

  @throws(classOf[TacticApplicationException])
  def introduceShadedZone(state:Proof) = {
    BY(Tactics.introduceShadedZone(0,_), state)
  }

  @throws(classOf[TacticApplicationException])
  def removeShadedZone(state:Proof)= {
    BY(Tactics.removeShadedZone(0,_), state)
  }

  @throws(classOf[TacticApplicationException])
  def trivialTautology(state:Proof)= {
    BY(Tactics.trivialTautology(0,_), state)
  }

}
