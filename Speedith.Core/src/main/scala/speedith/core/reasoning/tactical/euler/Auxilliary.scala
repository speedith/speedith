package speedith.core.reasoning.tactical.euler

import speedith.core.lang.{CompoundSpiderDiagram, Operator, Region, Zone}
import speedith.core.reasoning.Proof
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import speedith.core.reasoning.util.unitary.CorrespondingRegions

import scala.collection.JavaConversions._

/**
 * Helper functions and predicates for the use with [[BasicTacticals basic tacticals]]
  * and [[SimpleTacticals simple tacticals]].
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

  def isConjunctionWithShadingToCopy(sd : SpiderDiagramOccurrence ) : Boolean = sd match {
    case sd: CompoundSpiderDiagramOccurrence => sd.getOperator match {
      case Operator.Conjunction => {
        if (sd.getOperands.forall(_.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
          val op0 = sd.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op1 = sd.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          if (op0.getAllContours.subsetOf(op1.getAllContours)) {
            val leftRegions = computeCorrespondingShadedRegions(op0,op1)
            if (leftRegions.nonEmpty) { true }
            else {
              if (op1.getAllContours.subsetOf(op0.getAllContours)) {
                val rightRegions = computeCorrespondingShadedRegions(op1,op0)
                rightRegions.nonEmpty
              } else false
            }
          } else {
            if (op1.getAllContours.subsetOf(op0.getAllContours)) {
              val rightRegions = computeCorrespondingShadedRegions(op1,op0)
              rightRegions.nonEmpty
            } else false
          }
        } else false
      }
      case _ => false
    }
    case _ => false
  }

  def computeCorrespondingShadedRegions(d1 :PrimarySpiderDiagramOccurrence, d2 : PrimarySpiderDiagramOccurrence) : Set[Region] = {
    val visibleShadedZones = d1.getShadedZones & d1.getPresentZones
    val nonEmptyShadedRegions = visibleShadedZones.subsets.toSet.filter(s => s.nonEmpty)
    nonEmptyShadedRegions.map(region => CorrespondingRegions(d1.getPrimaryDiagram, d2.getPrimaryDiagram).correspondingRegion(new Region(region))).filter(r => r.zones.nonEmpty)
  }
  def computeMaximalCorrespondingShadedRegion(d1 : PrimarySpiderDiagramOccurrence, d2 : PrimarySpiderDiagramOccurrence): Option[(Set[Zone], Set[Zone])] = {
    val shadedZones = (d1.getShadedZones & d1.getPresentZones).toSet
    val nonEmptyShadedRegions = shadedZones.subsets.toSet.filter(s => s.nonEmpty)
    val regions = nonEmptyShadedRegions.map(region => Tuple2(region, CorrespondingRegions(d1.getPrimaryDiagram, d2.getPrimaryDiagram).correspondingRegion(new Region(region)).zones)).filter(m => m._2.nonEmpty)
    maxCorrespondingRegion(regions.to[collection.immutable.List])
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

  def equalContourSetsInEachPrimaryDiagram(subgoalIndex : Int) :Proof => Boolean = (state:Proof) => {
    val goal = state.getLastGoals.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val subDiagams = ReasoningUtils.getPrimaryDiagrams(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0))
      subDiagams.map(pd => pd.getAllContours.toSet).forall(subDiagams.head.getAllContours.toSet.sameElements)
    } else {
      false
    }
  }

  def maxCorrespondingRegion(regionMatch: List[(Set[Zone], Set[Zone])]) : Option[(Set[Zone], Set[Zone])]  = regionMatch match {
    case Nil => None
    case (r1:Set[Zone], r2:Set[Zone]) :: Nil => Some(r1,r2)
    case m1 :: m2 :: rest => maxCorrespondingRegion( (if (m1._2.size > m2._2.size ) m1 else m2) :: rest )
  }
}
