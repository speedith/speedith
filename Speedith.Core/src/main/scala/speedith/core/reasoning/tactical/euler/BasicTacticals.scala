package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import speedith.core.reasoning.tactical.TacticApplicationException


/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object BasicTacticals {
  def THEN(tac1: Proof => Seq[Proof], tac2: Proof => Seq[Proof]) = (state : Proof) => {
    tac1(state) flatMap tac2
  }

  def ORELSE(tac1 : Proof => Seq[Proof], tac2 : Proof => Seq[Proof]) = (state : Proof) => {
    val state1 = tac1(state)
    if (state1.isEmpty) {
      tac2(state)
    } else {
      state1
    }
  }

  def id (state : Proof) = {
    Seq(state)
  }

  def REPEAT(tac : Proof => Seq[Proof]): (Proof => Seq[Proof]) = (state : Proof) => {
    ORELSE(THEN(tac, REPEAT(tac)), id )(state)
  }

  @throws(classOf[TacticApplicationException])
  def BY( tac : Proof => Seq[Proof], state:Proof): Proof =  {
      tac(state).headOption.getOrElse{
        throw new TacticApplicationException("Tactic could not be applied to current subgoal")
      }
  }

}
