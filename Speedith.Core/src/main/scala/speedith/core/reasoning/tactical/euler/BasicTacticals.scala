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
  def THEN(tac1: Tactical, tac2: Tactical) = (name:String) => (state : Proof) => {
    tac1(name)(state) flatMap tac2(name)
  }

  def ORELSE(tac1 : Tactical, tac2 : Tactical) = (name:String) => (state : Proof) => {
    val state1 = tac1(name)(state)
    if (state1.isEmpty) {
      tac2(name)(state)
    } else {
      state1
    }
  }

  def id:Tactical = (name:String) => (state:Proof) => {
    Some(state)
  }

  def fail:Tactical = (name:String) =>(state:Proof) => {
    None
  }

  def TRY(tac : Tactical) = (name:String) => (state:Proof) => {
    ORELSE(tac, id)(name)(state)
  }

  def REPEAT(tac : Tactical): Tactical = (name:String) =>(state : Proof) => {
    ORELSE(THEN(tac, REPEAT(tac)), id )(name)(state)
  }

  def DEPTH_FIRST (predicate:Proof => Boolean, tac:Tactical):Tactical =  (name:String) => (state :Proof) => {
    if (predicate(state)) {
      id(name)(state)
    } else {
      THEN(tac, DEPTH_FIRST(predicate, tac))(name)(state)
    }
  }

  @throws(classOf[TacticApplicationException])
  def BY( tac : Tactical) = (name:String) => (state:Proof) =>  {
      tac(name)(state)
  }

}
