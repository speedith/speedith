package speedith.core.reasoning.tactical.euler


import speedith.core.lang.{PrimarySpiderDiagram, SpiderDiagram, CompoundSpiderDiagram, Operator}
import speedith.core.reasoning.Goals
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules.util.ReasoningUtils
import speedith.core.reasoning.tactical._
import scala.collection.JavaConversions._
import speedith.core.reasoning.tactical.euler.Auxiliary._
/**
  * Predicate functions to select possible target diagrams for the application of single rule tactics (see [[RuleTactics]])
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object Predicates {

  def containsContours : DiagramPredicate = {
    case d : PrimarySpiderDiagramOccurrence => d.getAllContours.nonEmpty
    case _ => false
  }

  def isImplication : DiagramPredicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Implication => true
      case _ => false
    }
    case _ => false
  }

  def isIdempotent : DiagramPredicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction | Operator.Disjunction | Operator.Equivalence | Operator.Implication =>
        sd.getOperand(0).getDiagram.equals(sd.getOperand(1).getDiagram)
      case _ => false
    }
    case _ => false
  }

  def isOperandOf(csd:CompoundSpiderDiagramOccurrence):  DiagramPredicate = {
    case sd:PrimarySpiderDiagramOccurrence => csd.getOperands map (_.getOccurrenceIndex) contains sd.getOccurrenceIndex
    case _ => false
  }

  def is(csd:PrimarySpiderDiagramOccurrence) : DiagramPredicate = {
    case sd:PrimarySpiderDiagramOccurrence => csd.getOccurrenceIndex == sd.getOccurrenceIndex
    case _ => false
  }

  def isPrimaryAndContainsMoreContours :  Set[String] => DiagramPredicate = (contours : Set[String]) =>  {
    case sd:PrimarySpiderDiagramOccurrence => (contours -- sd.getAllContours).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsMissingZones: DiagramPredicate =  {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones--sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsShadedZones : DiagramPredicate = {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones & sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsContours : DiagramPredicate = {
    case sd:PrimarySpiderDiagramOccurrence => sd.getAllContours.nonEmpty
    case _ => false
  }

  def isConjunctionOfPrimaryDiagramsWithEqualZoneSets : DiagramPredicate = {
    case sd: PrimarySpiderDiagramOccurrence => false
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0: PrimarySpiderDiagramOccurrence, op1: PrimarySpiderDiagramOccurrence) =>
          op0.getPresentZones.equals(op1.getPresentZones)
        case _ => false
      }
      case _ => false
    }
  }

  def isConjunctionWithContoursToCopy : DiagramPredicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match  {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0: PrimarySpiderDiagramOccurrence, op1: PrimarySpiderDiagramOccurrence) =>
          (op0.getAllContours -- op1.getAllContours).nonEmpty || (op1.getAllContours -- op0.getAllContours).nonEmpty
        case _ => false
      }
      case _ => false
    }
    case _ => false
  }

  def isConjunctionWithShadingToCopy : DiagramPredicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0: PrimarySpiderDiagramOccurrence, op1: PrimarySpiderDiagramOccurrence) =>
          if (containsCorrespondingShadedRegions(op0, op1)) {
            true
          } else {
            containsCorrespondingShadedRegions(op1,op0)
          }
        case _ => false
      }
      case _=> false
    }
    case _ => false
  }

  def isConjunctionContainingMissingZonesToCopy : DiagramPredicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0:PrimarySpiderDiagramOccurrence, op1:PrimarySpiderDiagramOccurrence) =>
          if (isCorrespondingMissingRegion(op0,op1)) {
            true
          } else {
            isCorrespondingMissingRegion(op1,op0)
          }
        case _ => false
      }
      case _ => false
    }
    case _ => false
  }

  def containsGivenContours : Set[String] => DiagramPredicate  = (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours & contours).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  def containsOtherContours :  Set[String] => DiagramPredicate  = (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours -- contours).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  def containsLessContours: Set[String] => DiagramPredicate  = (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => ( contours -- d.getAllContours ).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  /**
    * Combines two predicates to compute their conjunction
    *
    * @param p1 predicate 1
    * @param p2 predicate 2
    * @return the conjunction of predicate 1 and predicate 2
    */

  def AND (p1 : DiagramPredicate, p2: DiagramPredicate) : DiagramPredicate = (sd:SpiderDiagramOccurrence) => {
    p1(sd) && p2(sd)
  }


  def containsNoDiagramsWithShadedZonesThatCouldBeCopied: GoalPredicate = (state:Goals) => (subGoalIndex:Int) =>{
    if (state.isEmpty) {
      true
    } else {
      val goal = state.getGoalAt(subGoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        !hasDiagramWithMissingZonesThatCouldBeCopied(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0))
      } else {
        true
      }
    }
  }

  private def hasDiagramWithMissingZonesThatCouldBeCopied(sd : SpiderDiagram) :Boolean = sd match {
    case sd: PrimarySpiderDiagram => false
    case sd: CompoundSpiderDiagram => (sd.getOperator, sd.getOperand(0), sd.getOperand(1)) match {
      case (Operator.Conjunction, op0: PrimarySpiderDiagram, op1: PrimarySpiderDiagram) =>
        op0.getAllContours.subsetOf(op1.getAllContours) && (op0.getShadedZones -- op0.getPresentZones).nonEmpty ||
          op1.getAllContours.subsetOf(op0.getAllContours) && (op1.getShadedZones -- op1.getPresentZones).nonEmpty
      case (Operator.Conjunction, _, _) => hasDiagramWithMissingZonesThatCouldBeCopied(sd.getOperand(0)) || hasDiagramWithMissingZonesThatCouldBeCopied(sd.getOperand(1))
      case _ => false
    }
  }

  def equalContourSetsInEachPrimaryDiagram: GoalPredicate = (state:Goals) => (subgoalIndex : Int) =>{
    val goal = state.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val subDiagams = ReasoningUtils.getPrimaryDiagrams(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0))
      subDiagams map (pd => pd.getAllContours.toSet) forall subDiagams.head.getAllContours.toSet.sameElements
    } else {
      false
    }
  }

  def isUnitaryDiagram: GoalPredicate = (state:Goals) => (subGoalIndex : Int) => {
    if (state.isEmpty) {
      true
    } else {
      val goal = state.getGoalAt(subGoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0).isInstanceOf[PrimarySpiderDiagram]
      } else {
        false
      }
    }
  }
}
