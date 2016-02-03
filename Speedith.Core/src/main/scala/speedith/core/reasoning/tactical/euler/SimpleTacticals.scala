package speedith.core.reasoning.tactical.euler

import speedith.core.lang.{CompoundSpiderDiagram, PrimarySpiderDiagram, SpiderDiagram}
import speedith.core.reasoning.Proof
import BasicTacticals._
import Tactics._
import speedith.core.reasoning.rules.util.ReasoningUtils
import scala.collection.JavaConversions._

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


  private def equalContourSetsInEachPrimaryDiagram(subgoalIndex : Int) :Proof => Boolean = (state:Proof) => {
    val goal = state.getLastGoals.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val subDiagams = ReasoningUtils.getPrimaryDiagrams(goal)
      subDiagams.map(pd => pd.getAllContours.toSet).forall(subDiagams.head.getAllContours.sameElements)
    } else {
      false
    }
  }

  def unifyContourSets(state:Proof) = {
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(0),  ORELSE(trivialTautology(0,_),introduceContour(0,_)))(state)
  }
}
