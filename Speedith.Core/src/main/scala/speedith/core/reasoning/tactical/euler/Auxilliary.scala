package speedith.core.reasoning.tactical.euler

import speedith.core.lang._
import speedith.core.reasoning.Goals
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import speedith.core.reasoning.tactical.{Chooser, Predicate, TacticApplicationException}
import speedith.core.reasoning.util.unitary.CorrespondingRegions

import scala.collection.JavaConversions._

/**
 * Helper functions and predicates for the use with [[speedith.core.reasoning.tactical.Tacticals basic tacticals]]
  * and [[BasicTactics simple tacticals]].
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object Auxilliary {


  def collectDiagramsWithMissingZonesThatCouldBeCopied(subGoalIndex: Int, state : Goals): Set[SpiderDiagramOccurrence ] =  {
    val target =getSubGoal(subGoalIndex, state)
    val result = getDiagramWithMissingZonesThatCouldBeCopied(target.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0))
    result
  }

  def getDiagramWithMissingZonesThatCouldBeCopied(sd : SpiderDiagramOccurrence) :Set[SpiderDiagramOccurrence] = sd match {
    case sd: PrimarySpiderDiagramOccurrence => Set()
    case sd: CompoundSpiderDiagramOccurrence => (sd.getOperator, sd.getOperand(0), sd.getOperand(1)) match {
      case (Operator.Conjunction, op0: PrimarySpiderDiagramOccurrence, op1: PrimarySpiderDiagramOccurrence) =>
        (op0.getAllContours.subsetOf(op1.getAllContours) && (op0.getShadedZones -- op0.getPresentZones).nonEmpty,
          op1.getAllContours.subsetOf(op0.getAllContours) && (op1.getShadedZones -- op1.getPresentZones).nonEmpty) match {
          case (false, false) => Set()
          case (true, false) => Set(op0)
          case (false, true) => Set(op1)
          case (true, true) => Set(op0, op1)
        }

      case (Operator.Conjunction, _, _) => getDiagramWithMissingZonesThatCouldBeCopied(sd.getOperand(0)) ++ getDiagramWithMissingZonesThatCouldBeCopied(sd.getOperand(1))
      case _ => Set()
    }
  }

  def containsNoDiagramsWithShadedZonesThatCouldBeCopied: Goals =>Int => Boolean = (state:Goals) => (subGoalIndex:Int) =>{
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

  def containsCorrespondingShadedRegions(d1 : PrimarySpiderDiagramOccurrence, d2: PrimarySpiderDiagramOccurrence) : Boolean = {
    // to maximise the effect of copying and to somewhat counter the explosion of possible regions
    // we bundle the shaded zones according to their in-sets (the sets they are contained in).
    // The outer zone is element of all those regions so that it can be copied as well
    val shadedRight = (d2.getShadedZones & d2.getPresentZones).toSet
    val contoursLeft = d1.getAllContours
    val shadedZones = (d1.getShadedZones & d1.getPresentZones).toSet
    val shadedRegionsPerContour = contoursLeft.map(c => shadedZones.filter(z => z.getInContours.contains(c) || z.getInContours.isEmpty)).filter(_.nonEmpty)
    val regionsRight = shadedRegionsPerContour map (r => CorrespondingRegions(d1.getPrimaryDiagram, d2.getPrimaryDiagram).correspondingRegion(new Region(r)).zones)
    val nonShadedRight = regionsRight filterNot (r => r.subsetOf(shadedRight))
    nonShadedRight exists (_.nonEmpty)
  }

  def isCorrespondingMissingRegion(d1:PrimarySpiderDiagramOccurrence, d2 : PrimarySpiderDiagramOccurrence) : Boolean  = {
    // to maximise the effect of copying and to somewhat counter the explosion of possible regions
    // we bundle the shaded zones according to their in-sets (the sets they are contained in).
    // The outer zone is element of all those regions so that it can be copied as well
    val shadedRegionRight = (d2.getShadedZones & d2.getPresentZones).toSet
    val contoursLeft = d1.getAllContours
    val missingZones = (d1.getShadedZones -- d1.getPresentZones).toSet
    val missingRegionsPerContour = contoursLeft map (c => missingZones filter(_.getInContours.contains(c))) filter (_.nonEmpty)
    missingRegionsPerContour exists (r => CorrespondingRegions(d1.getPrimaryDiagram, d2.getPrimaryDiagram).correspondingRegion(new Region(r)).zones.nonEmpty)
  }

  def getCorrespondingShadedRegion(d1 : PrimarySpiderDiagramOccurrence, d2:PrimarySpiderDiagramOccurrence): Option[(Set[Zone], Set[Zone])] = {
    // to maximise the effect of copying and to somewhat counter the explosion of possible regions
    // we bundle the shaded zones according to their in-sets (the sets they are contained in).
    // The outer zone is element of all those regions so that it can be copied as well
    val contoursLeft = d1.getAllContours
    val shadedZones = (d1.getShadedZones & d1.getPresentZones).toSet
    val shadedRegionsPerContour = contoursLeft map (c => shadedZones filter (z => z.getInContours.contains(c) ||z.getInContours.isEmpty)) filter (_.nonEmpty)
    val regions = shadedRegionsPerContour map (region => Tuple2(region, CorrespondingRegions(d1.getPrimaryDiagram, d2.getPrimaryDiagram).correspondingRegion(new Region(region)).zones)) filter (m => m._2.nonEmpty)
    val unShadedTargets = regions filter (_._2.exists((d2.getPresentZones -- d2.getShadedZones).contains ))
    maxCorrespondingRegion(unShadedTargets.to[collection.immutable.List])
  }


  def getContoursInConclusion(subgoalIndex : Int, state:Goals) : Set[String]= {
    if (state.isEmpty) {
      Set()
    } else {
      val goal = state.getGoalAt(subgoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        AutomaticUtils.collectContours(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(1)).toSet
      } else {
        Set()
      }
    }
  }

  def getContoursInSubGoal(subgoalIndex: Int, state:Goals) : Set[String]= {
    val goal = state.getGoalAt(subgoalIndex)
    AutomaticUtils.collectContours(goal).toSet
  }

  def collectContours(diagram : SpiderDiagramOccurrence) : Set[String] = diagram match {
    case diagram:PrimarySpiderDiagramOccurrence => diagram.getAllContours.toSet
    case diagram : CompoundSpiderDiagramOccurrence => (diagram.getOperands flatMap collectContours).toSet
  }

  def collectShadedZones(diagram: SpiderDiagram): Set[Zone] = diagram match {
    case diagram : PrimarySpiderDiagram => (diagram.getPresentZones & diagram.getShadedZones).toSet
    case diagram : CompoundSpiderDiagram => (diagram.getOperands flatMap collectShadedZones).toSet
  }

  def getShadedZonesInConclusion(subgoalIndex : Int, state : Goals) : Set[Zone] = {
    if (state.isEmpty) {
      Set()
    } else {
      val goal = state.getGoalAt(subgoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        collectShadedZones(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(1))
      } else {
        Set()
      }
    }
  }

  def collectUnShadedZones(diagram: SpiderDiagram): Set[Zone] =  diagram match {
    case diagram : PrimarySpiderDiagram => (diagram.getPresentZones -- diagram.getShadedZones).toSet
    case diagram : CompoundSpiderDiagram => (diagram.getOperands flatMap collectUnShadedZones).toSet
  }

  def getUnshadedZonesInConclusion(subgoalIndex : Int, state : Goals) : Set[Zone] = {
    if (state.isEmpty) {
      Set()
    } else {
      val goal = state.getGoalAt(subgoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        collectUnShadedZones(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(1))
      } else {
        Set()
      }
    }
  }

  def collectVisibleZones(diagram: SpiderDiagram): Set[Zone] = diagram match {
    case diagram : PrimarySpiderDiagram => diagram.getPresentZones.toSet
    case diagram : CompoundSpiderDiagram => (diagram.getOperands flatMap collectVisibleZones).toSet
  }

  def getVisibleZonesInConclusion(subGoalIndex: Int, state: Goals) : Set[Zone] = {
    if (state.isEmpty) {
      Set()
    } else {
      val goal = state.getGoalAt(subGoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        collectVisibleZones(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(1))
      } else {
        Set()
      }
    }
  }

  def equalContourSetsInEachPrimaryDiagram :Goals => Int =>Boolean = (state:Goals) => (subgoalIndex : Int) =>{
    val goal = state.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val subDiagams = ReasoningUtils.getPrimaryDiagrams(goal.asInstanceOf[CompoundSpiderDiagram].getOperand(0))
      subDiagams map (pd => pd.getAllContours.toSet) forall subDiagams.head.getAllContours.toSet.sameElements
    } else {
      false
    }
  }

  def getDeepestNestedDiagram(subgoalIndex: Int): Goals => Option[CompoundSpiderDiagramOccurrence] = (state:Goals) => {
    val goal = getSubGoal(subgoalIndex, state)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      getDeepestNestedDiagram(goal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0))
    } else {
      None
    }
  }

  def getDeepestNestedDiagram(sd: SpiderDiagramOccurrence) : Option[CompoundSpiderDiagramOccurrence] = sd match {
    case sd:PrimarySpiderDiagramOccurrence => None
    case sd:CompoundSpiderDiagramOccurrence => sd.getOperator match  {
      case Operator.Conjunction => (sd.getOperand(0), sd.getOperand(1)) match {
        case (op0:PrimarySpiderDiagramOccurrence, op1:PrimarySpiderDiagramOccurrence) => Some(sd)
        case (op0:CompoundSpiderDiagramOccurrence, _) => getDeepestNestedDiagram(op0)
        case (_, op1:CompoundSpiderDiagramOccurrence) => getDeepestNestedDiagram(op1)
      }
      case _ => None
    }
  }

  def isSingleUnitaryDiagram(subGoalIndex:Int) : Goals => Boolean = (state:Goals) => {
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

  def isUnitaryDiagram: Goals => Int => Boolean = (state:Goals) => (subGoalIndex : Int) => {
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

  def maxCorrespondingRegion(regionMatch: List[(Set[Zone], Set[Zone])]) : Option[(Set[Zone], Set[Zone])]  = regionMatch match {
    case Nil => None
    case (r1:Set[Zone], r2:Set[Zone]) :: Nil => Some(r1,r2)
    case m1 :: m2 :: rest => maxCorrespondingRegion( (if (m1._2.size > m2._2.size ) m1 else m2) :: rest )
  }

  /**
    * implements some general checks
    *
    * @param subgoalIndex the index of subgoal which shall be returned
    * @param goals the set of goals in which the subgoal will be searched
    */
  def getSubGoal(subgoalIndex : Int, goals: Goals): SpiderDiagramOccurrence = {
    if (goals == null || goals.getGoals == null)  throw new TacticApplicationException("Could not apply tactic")
    val goal = goals.getGoalAt(subgoalIndex)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      SpiderDiagramOccurrence.wrapDiagram(goal, 0)
    } else throw new TacticApplicationException("No subgoal for this tactic")
  }

  def firstMatchingDiagram(sd: SpiderDiagramOccurrence, predicate: Predicate): Option[SpiderDiagramOccurrence] = {
    if (predicate(sd)) {
      Some(sd)
    } else {
      sd match {
        case sd: CompoundSpiderDiagramOccurrence =>
          val matching = firstMatchingDiagram(sd.getOperand(0), predicate)
          matching match {
            case None => firstMatchingDiagram(sd.getOperand(1), predicate)
            case _ => matching
          }
        case sd: PrimarySpiderDiagramOccurrence => None
      }
    }
  }

  def firstMatchingDiagramTest(sd: SpiderDiagramOccurrence) :Predicate => Option[SpiderDiagramOccurrence] = (predicate:Predicate) =>{
    if (predicate(sd)) {
      Some(sd)
    } else {
      sd match {
        case sd: CompoundSpiderDiagramOccurrence =>
          val matching = firstMatchingDiagram(sd.getOperand(0), predicate)
          matching match {
            case None => firstMatchingDiagram(sd.getOperand(1), predicate)
            case _ => matching
          }
        case sd: PrimarySpiderDiagramOccurrence => None
      }
    }
  }
  def firstMatchingDiagramAndContour(sd: SpiderDiagramOccurrence,
                                     predicate: Predicate,
                                     contourChooser: Chooser[Set[String]])
  : Option[(SpiderDiagramOccurrence, Option[Set[String]])] = {
    if (predicate(sd)) {
      Some(Tuple2(sd, contourChooser(sd)))
    } else {
      sd match {
        case sd: CompoundSpiderDiagramOccurrence =>
          val matching = firstMatchingDiagramAndContour(sd.getOperand(0), predicate, contourChooser)
          matching match {
            case None => firstMatchingDiagramAndContour(sd.getOperand(1), predicate, contourChooser)
            case _ => matching
          }
        case sd: PrimarySpiderDiagramOccurrence => None
      }
    }
  }
}
