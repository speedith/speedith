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

  def isConjunction:DiagramPredicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => true
      case _ => false
    }
    case _ => false
  }

  def isDisjunction:DiagramPredicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Disjunction=> true
      case _ => false
    }
    case _ => false
  }

  def isNegation:DiagramPredicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Negation=> true
      case _ => false
    }
    case _ => false
  }


  def isAtPositivePosition(parent: SpiderDiagramOccurrence): DiagramPredicate = (sd : SpiderDiagramOccurrence) =>{
    if (sd.equals(parent)) {
      true
    } else {
      parent match {
        case parent:PrimarySpiderDiagramOccurrence => false
        case parent:CompoundSpiderDiagramOccurrence => parent.getOperator match {
          case Operator.Conjunction|Operator.Disjunction|Operator.Equivalence =>
            isAtPositivePosition(parent.getOperand(0))(sd) || isAtPositivePosition(parent.getOperand(1))(sd)
          case Operator.Implication =>
            isAtNegativePosition(parent.getOperand(0))(sd) || isAtPositivePosition(parent.getOperand(1))(sd)
          case Operator.Negation =>
            isAtNegativePosition(parent.getOperand(0))(sd)
        }
      }
    }
  }

  def isAtNegativePosition(parent: SpiderDiagramOccurrence): DiagramPredicate = (sd : SpiderDiagramOccurrence) =>{
    if (sd.equals(parent)) {
      false
    } else {
      parent match {
        case parent:PrimarySpiderDiagramOccurrence => false
        case parent:CompoundSpiderDiagramOccurrence => parent.getOperator match {
          case Operator.Conjunction|Operator.Disjunction|Operator.Equivalence =>
            isAtNegativePosition(parent.getOperand(0))(sd) || isAtNegativePosition(parent.getOperand(1))(sd)
          case Operator.Implication =>
            isAtPositivePosition(parent.getOperand(0))(sd) || isAtNegativePosition(parent.getOperand(1))(sd)
          case Operator.Negation =>
            isAtPositivePosition(parent.getOperand(0))(sd)
        }
      }
    }
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

  def containsNoDiagramsWithShadedZonesThatCouldBeCopied: GoalPredicate = (state:Goals) => (subGoalIndex:Int) =>{
    if (state.isEmpty) {
      true
    } else {
      val goal = state.getGoalAt(subGoalIndex)
      if (ReasoningUtils.isImplication(goal)) {
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
    if (ReasoningUtils.isImplication(goal)) {
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
      if (ReasoningUtils.isImplication(goal)) {
        goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0).isInstanceOf[PrimarySpiderDiagram]
      } else {
        false
      }
    }
  }

  def isSubGoalSolved: GoalPredicate = (state:Goals) => (subGoalIndex : Int) => {
    state.isEmpty || subGoalIndex >= state.getGoalsCount
  }

  def containsDisjunction : GoalPredicate =(state:Goals) => (subGoalIndex:Int) => {
    if (state.isEmpty) {
      false
    } else {
      val goal = getSubGoal(subGoalIndex, state)
      if (ReasoningUtils.isImplication(goal)) {
        val premiss  = firstMatchingDiagram(goal, isDisjunction)
        premiss match {
          case Some(diagram) => true
          case None => false
        }
      } else {
        false
      }
    }
  }

  def containsNegation : GoalPredicate = (state:Goals) => (subGoalIndex:Int) => {
    if (state.isEmpty) {
      false
    } else {
      val goal = getSubGoal(subGoalIndex, state)
      if (ReasoningUtils.isImplication(goal)) {
        val premiss  = firstMatchingDiagram(goal, isNegation)
        premiss match {
          case Some(diagram) => true
          case None => false
        }
      } else {
        false
      }
    }
  }

  def isEmptyGoalList : GoalPredicate = (state:Goals) => (subGoalIndex:Int) => {
    state.isEmpty
  }

}
