package speedith.core.reasoning.tactical.euler


import speedith.core.lang.Operator
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import scala.collection.JavaConversions._
import speedith.core.reasoning.tactical.euler.Auxilliary._
/**
  * Predicate functions to select possible target diagrams for the application of single rule tactics (see [[Tactics]])
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object Predicates {

  def containsContours : Predicate = {
    case d : PrimarySpiderDiagramOccurrence => d.getAllContours.nonEmpty
    case _ => false
  }

  def isImplication : Predicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Implication => true
      case _ => false
    }
    case _ => false
  }

  def isIdempotent : Predicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction | Operator.Disjunction | Operator.Equivalence | Operator.Implication =>
        sd.getOperand(0).getDiagram.equals(sd.getOperand(1).getDiagram)
      case _ => false
    }
    case _ => false
  }

  def isOperand(csd:CompoundSpiderDiagramOccurrence):  Predicate = {
    case sd:PrimarySpiderDiagramOccurrence => csd.getOperands.map(op => op.getOccurrenceIndex).contains(sd.getOccurrenceIndex)
    case _ => false
  }

  def isPrimaryAndContainsMoreContours :  Set[String] => Predicate = (contours : Set[String]) =>  {
    case sd:PrimarySpiderDiagramOccurrence => (contours -- sd.getAllContours).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsMissingZones: Predicate =  {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones--sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsShadedZones : Predicate = {
    case sd:PrimarySpiderDiagramOccurrence => (sd.getShadedZones & sd.getPresentZones).nonEmpty
    case _ => false
  }

  def isPrimaryAndContainsContours : Predicate = {
    case sd:PrimarySpiderDiagramOccurrence => sd.getAllContours.nonEmpty
    case _ => false
  }

  def isConjunctionOfPrimaryDiagramsWithEqualZoneSets : Predicate = {
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

  def isConjunctionWithContoursToCopy : Predicate = {
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

  def isConjunctionWithShadingToCopy : Predicate = {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0: PrimarySpiderDiagramOccurrence, op1: PrimarySpiderDiagramOccurrence) =>
          /* if (op0.getAllContours.subsetOf(op1.getAllContours)) {
            val leftRegions = computeCorrespondingShadedRegions(op0, op1)
            if (leftRegions.nonEmpty) {
              true
            }
            else {
              if (op1.getAllContours.subsetOf(op0.getAllContours)) {
                val rightRegions = computeCorrespondingShadedRegions(op1, op0)
                rightRegions.nonEmpty
              } else false
            }
          } else {
            if (op1.getAllContours.subsetOf(op0.getAllContours)) {
              val rightRegions = computeCorrespondingShadedRegions(op1, op0)
              rightRegions.nonEmpty
            } else false
          } */
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

  def isConjunctionContainingMissingZonesToCopy : Predicate = {
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0:PrimarySpiderDiagramOccurrence, op1:PrimarySpiderDiagramOccurrence) =>
        /*  val miss1 = computeCorrespondingMissingRegions(op0,op1)
         if (miss1.nonEmpty) {
           true
         } else {
           computeCorrespondingMissingRegions(op1,op0).nonEmpty
         }
         */
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

  def containsGivenContours : Set[String] => Predicate  = (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours & contours).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  def containsOtherContours :  Set[String] => Predicate  =  (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => (d.getAllContours -- contours).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  def containsLessContours: Set[String] => Predicate  =  (contours : Set[String]) => {
    case d: PrimarySpiderDiagramOccurrence => ( contours -- d.getAllContours ).nonEmpty
    case d: CompoundSpiderDiagramOccurrence => false
  }

  /**
    * Combines two predicates to compute their conjunction
    * @param p1 predicate 1
    * @param p2 predicate 2
    * @return the conjunction of predicate 1 and predicate 2
    */

  def AND (p1 : Predicate, p2: Predicate) : Predicate = (sd:SpiderDiagramOccurrence) => {
    p1(sd) && p2(sd)
  }
}
