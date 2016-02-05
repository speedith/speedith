package speedith.core.reasoning.tactical.euler

import speedith.core.lang.{CompoundSpiderDiagram, PrimarySpiderDiagram, SpiderDiagram}
import speedith.core.reasoning.Proof
import BasicTacticals._
import Tactics._
import speedith.core.reasoning.automatic.wrappers.{PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules.util.ReasoningUtils
import scala.collection.JavaConversions._
import Auxilliary._

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object SimpleTacticals {

  def vennify(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      introduceShadedZone(0,_)))(state)
  }

  def deVennify (state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),removeShadedZone(0,_)))(state)
  }


  private def equalContourSetsInEachPrimaryDiagram(subgoalIndex : Int) :Proof => Boolean = (state:Proof) => {
    val goal = state.getLastGoals.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val subDiagams = ReasoningUtils.getPrimaryDiagrams(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0))
      subDiagams.map(pd => pd.getAllContours.toSet).forall(subDiagams.head.getAllContours.toSet.sameElements)
    } else {
      false
    }
  }



  def unifyContourSets(state:Proof) = {
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(0),  ORELSE(trivialTautology(0,_),introduceContour(0,_)))(state)
  }

  def eraseAllContours(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      eraseContour(0,containsContours, anyContour,_)))(state)
  }

  def combineAll(state : Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      combine(0,_)))(state)
  }

  def vennStyle(state : Proof) = {
    THEN(unifyContourSets, THEN(vennify, THEN(combineAll, deVennify)))(state)
  }

  def matchConclusion(state : Proof) = {
    val concContours =getContoursInConclusion(0,state)
    THEN(REPEAT(ORELSE(trivialTautology(0,_), removeShadedZone(0,_))), REPEAT(ORELSE(trivialTautology(0,_),
      eraseContour(0, containsOtherContours(_, concContours ), firstOfTheOtherContours(_, concContours),_))))(state)
  }

  def copyTopologicalInformation(state : Proof) = {

  }
}