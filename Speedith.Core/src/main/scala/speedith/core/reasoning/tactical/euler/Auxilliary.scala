package speedith.core.reasoning.tactical.euler

import speedith.core.lang.{Operator, CompoundSpiderDiagram}
import speedith.core.reasoning.Proof
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}

import scala.collection.JavaConversions._

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object Auxilliary {

  def containsContours(d : SpiderDiagramOccurrence) : Boolean = d match {
    case d : PrimarySpiderDiagramOccurrence => d.getAllContours.nonEmpty
    case _ => false
  }

  def isImplication (sd : SpiderDiagramOccurrence): Boolean = sd match {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Implication => true
      case _ => false
    }
    case _ => false
  }

  def isPrimaryAndContainsMoreContours(sd : SpiderDiagramOccurrence, contours : Set[String]) : Boolean = sd match {
    case sd:PrimarySpiderDiagramOccurrence => (contours -- sd.getAllContours).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsMissingZones(sd : SpiderDiagramOccurrence) : Boolean = sd match {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones--sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsShadedZones(sd : SpiderDiagramOccurrence) : Boolean = sd match {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones & sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsContours(sd : SpiderDiagramOccurrence) : Boolean = sd match {
    case sd:PrimarySpiderDiagramOccurrence => sd.getAllContours.nonEmpty
    case _ => false
  }

  def isConjunctionOfPrimaryDiagramsWithEqualZoneSets(sd : SpiderDiagramOccurrence) : Boolean = sd match {
    case sd: PrimarySpiderDiagramOccurrence => false
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => {
        if (sd.getOperand(0).isInstanceOf[PrimarySpiderDiagramOccurrence] && sd.getOperand(1).isInstanceOf[PrimarySpiderDiagramOccurrence]) {
          val op1 = sd.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op2 = sd.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          op1.getPresentZones.equals(op2.getPresentZones)

        } else {false}
      }
      case _ => false
    }
  }

  def isConjunctionWithContoursToCopy(sd : SpiderDiagramOccurrence ) : Boolean = sd match {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => {
        if (sd.getOperands.forall(_.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
          val op0 = sd.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op1 = sd.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          (op0.getAllContours -- op1.getAllContours).nonEmpty || (op1.getAllContours -- op0.getAllContours).nonEmpty
        } else false
      }
      case _ => false
    }
    case _ => false
  }


  def containsGivenContours(d : SpiderDiagramOccurrence, contours : Set[String]) : Boolean = d match {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours & contours).nonEmpty
  }

  def containsOtherContours(d : SpiderDiagramOccurrence, contours : Set[String]) : Boolean = d match {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours -- contours).nonEmpty
  }

  def firstOfTheGivenContours(sd : SpiderDiagramOccurrence , contours : Set[String]) : Option[String] = sd match {
    case sd : CompoundSpiderDiagramOccurrence => None
    case sd : PrimarySpiderDiagramOccurrence => Some((sd.getAllContours & contours).head)
  }

  def firstOfTheOtherContours(sd: SpiderDiagramOccurrence, contours: Set[String]): Option[String] = sd match {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence => Some((sd.getAllContours -- contours).head)
  }

  def anyContour(sd: SpiderDiagramOccurrence): Option[String] = sd match {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      try {
        Some(sd.getAllContours.head)
      }
      catch {
        case e: Exception => None
      }
  }

  def getContoursInConclusion(subgoalIndex : Int, state : Proof) : Set[String]= {
    val goal = state.getLastGoals.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      AutomaticUtils.collectContours(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(1)).toSet
    } else {
      Set()
    }
  }
}
