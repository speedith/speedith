package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import speedith.core.reasoning.tactical.TacticApplicationException


/**
 * Basic tacticals to combine other tacticals.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object BasicTacticals {
  def THEN(tac1: Tactical, tac2: Tactical) = (state : Proof) => {
    tac1(state) flatMap tac2
  }

  def ORELSE(tac1 : Tactical, tac2 : Tactical) = (state : Proof) => {
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

  def fail(state:Proof) = {
    Seq()
  }

  def TRY(tac : Tactical) = (state:Proof) => {
    ORELSE(tac, id)(state)
  }

  def REPEAT(tac : Tactical): Tactical = (state : Proof) => {
    ORELSE(THEN(tac, REPEAT(tac)), id )(state)
  }

  def DEPTH_FIRST (predicate:Proof => Boolean, tac:Tactical):Tactical = (state :Proof) => {
    if (predicate(state)) {
      id(state)
    } else {
      THEN(tac, DEPTH_FIRST(predicate, tac))(state)
    }
  }

  @throws(classOf[TacticApplicationException])
  def BY( tac : Tactical) = (state:Proof) =>  {
      tac(state).headOption.getOrElse{
        throw new TacticApplicationException("Tactic could not be applied to current subgoal")
      }
  }

}
