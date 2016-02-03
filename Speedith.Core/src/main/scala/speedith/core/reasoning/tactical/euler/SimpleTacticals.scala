package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import BasicTacticals._
import Tactics._

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object SimpleTacticals {

  def vennify(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      ORELSE(introduceShadedZone(0,_),
        introduceContour(0,_) )))(state)
  }

  def deVennify (state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),removeShadedZone(0,_)))(state)
  }
}
