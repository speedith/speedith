package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang.{CompoundSpiderDiagram, Operator, PrimarySpiderDiagram, Region, SpiderDiagram, Zone}
import speedith.core.reasoning.InferenceRule
import speedith.core.reasoning.args.{MultipleRuleArgs, RuleArg}
import speedith.core.reasoning.automatic.rules._
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules._
import speedith.core.reasoning.util.unitary.CorrespondingRegions

import scala.collection.JavaConversions._
import scala.collection.mutable

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
object AutomaticUtils {

  // <editor-fold defaultstate="collapsed" desc="Various helper methods">

  def collectContours  (spiderDiagram: SpiderDiagram) : java.util.Collection[String] = spiderDiagram  match {
    case spiderDiagram : PrimarySpiderDiagram => spiderDiagram.getAllContours
    case spiderDiagram: CompoundSpiderDiagram => spiderDiagram.getOperands.flatMap(collectContours)
  }

  def isConjunctive(sd : SpiderDiagram) : Boolean =  sd match {
    case sd : PrimarySpiderDiagram => true
    case sd : CompoundSpiderDiagram => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  def regionWithNewContours(region: Iterable[Zone], contoursToAdd: Set[String] ): Set[Zone] = {
    val powSetContours = contoursToAdd.subsets.toSet
    powSetContours.flatMap(c  => region.map(zone => new Zone(zone.getInContours ++ c, zone.getOutContours ++ (contoursToAdd -- c))).toSet ++ region.map(zone => new Zone(zone.getInContours ++ (contoursToAdd -- c), zone.getOutContours ++ c)))
  }

  def containsEmptyZone (sd : SpiderDiagram): Boolean = sd match {
    case sd:PrimarySpiderDiagram =>
      sd.getAllContours.exists(c => sd.getPresentZones.forall(!_.getInContours.contains(c)))
    case sd: CompoundSpiderDiagram =>
      sd.getOperands.exists(containsEmptyZone)
  }
  // </editor-fold>

  // <editor-fold defaultstate="collapsed" desc="Creation of possible rule applications">
  /**
   * Creates all possible rule application for the given SpiderDiagram with respect to the given set of contours.
   *
   * @param target The SpiderDiagramOccurrence for which the set of PossibleInferenceApplication will be created
   * @param contours The set of contours present in the whole subgoal target is contained in
   * @return A set of PossibleInferenceApplication denoting all rule applications possible to target
   */
  def createAllPossibleRuleApplications(subGoalIndex:Int, target: SpiderDiagramOccurrence, contours: util.Collection[String]):java.util.Set[_ <: PossibleInferenceApplication[_ <: RuleArg]]  = {
   createAllPossibleRuleApplicationsRec(subGoalIndex, target, contours)
  }


  private def createAllPossibleRuleApplicationsRec (subGoalIndex:Int, target: SpiderDiagramOccurrence, contours: util.Collection[String]):Set[_ <: PossibleInferenceApplication[_ <: RuleArg]] = target match {
    case target : PrimarySpiderDiagramOccurrence =>
      createRemoveShadedZoneApplications(subGoalIndex, target) ++
        createRemoveShadingApplications(subGoalIndex,target) ++
        createIntroducedShadedZoneApplications(subGoalIndex,target) ++
        createRemoveContourApplications(subGoalIndex,target) ++
        createIntroduceContoursApplication(subGoalIndex,target, contours)
    case target : CompoundSpiderDiagramOccurrence =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>
        createCopyContourApplications(subGoalIndex,target) ++
          createCopyShadingApplications(subGoalIndex,target) ++
          createCombiningApplications(subGoalIndex,target) ++
          createAllPossibleRuleApplicationsRec(subGoalIndex,target.getOperand(0), contours) ++
          createAllPossibleRuleApplicationsRec(subGoalIndex,target.getOperand(1), contours) ++
          createConjunctionEliminationApplication(subGoalIndex,target)
      case Operator.Implication => createAllPossibleRuleApplicationsRec(subGoalIndex,target.getOperand(0), contours)
      case _ => Set()
    }
    case _ => Set() //TODO: full implementation for Compound Diagrams!
  }



  private def createConjunctionEliminationApplication(subGoalIndex: Int, target: CompoundSpiderDiagramOccurrence) : Set[PossibleConjunction] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => Set() +
      new PossibleConjunction(subGoalIndex, target, new ConjunctionElimination(), target.getOperand(0)) +
      new PossibleConjunction(subGoalIndex, target, new ConjunctionElimination(), target.getOperand(1))
    case _ => Set();
  }

  private def createCopyContourApplications(subGoalIndex: Int, target: CompoundSpiderDiagramOccurrence) : Set[PossibleCopyContour] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val difference =  leftContours -- rightContours
      (( leftContours -- rightContours)
          .map(c => new PossibleCopyContour(subGoalIndex,target.getOperand(0), new CopyContoursTopological(), c)) ++
        (rightContours -- leftContours)
          .map(c => new PossibleCopyContour(subGoalIndex,target.getOperand(1), new CopyContoursTopological(), c))).toSet
    } else {
      Set()
    }
  }

  private def createCopyShadingApplications(subGoalIndex : Int, target: CompoundSpiderDiagramOccurrence) : Set[PossibleCopyShading] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftDiagram = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram]
      val rightDiagram = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram]
      val leftContours= leftDiagram.getAllContours
      val rightContours = rightDiagram.getAllContours
      if (leftContours.subsetOf(rightContours) || rightContours.subsetOf(leftContours)) {
//        val contoursOnlyInLeft = leftContours -- rightContours
//        val contoursOnlyInRight = rightContours -- leftContours
        val leftVisibleShadedZones = leftDiagram.getShadedZones & leftDiagram.getPresentZones
        val leftNonEmptyShadedRegions = leftVisibleShadedZones.subsets.toSet.filter(s => s.nonEmpty)
        val leftRegions = leftNonEmptyShadedRegions.map(region => Tuple2(region, CorrespondingRegions(leftDiagram, rightDiagram).correspondingRegion(new Region(region)))).filter(r => r._2.zones.nonEmpty)
        val leftResult = leftRegions.
              map(r => new PossibleCopyShading(subGoalIndex,target.getOperand(0), new CopyShading(), r._1))
        val rightShadedRegions = (rightDiagram.getShadedZones & rightDiagram.getPresentZones)
          .subsets.toSet.filter(r => r.nonEmpty)
        val rightRegions = rightShadedRegions.
          map(r => Tuple2(r, CorrespondingRegions(rightDiagram, leftDiagram).correspondingRegion(new Region(r)))).filter(t => t._2.zones.nonEmpty)
        val rightResult = rightRegions.
          map(r => new PossibleCopyShading(subGoalIndex,target.getOperand(1), new CopyShading(), r._1))
        leftResult ++ rightResult
      }
      else {
        Set()
      }
    } else {
      Set()
    }
  }

  private def createCombiningApplications(subGoalIndex : Int,target: CompoundSpiderDiagramOccurrence) : Set[PossibleCombining] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftZones = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      val rightZones = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      if (leftZones.equals(rightZones)) {
        Set() + new PossibleCombining(subGoalIndex,target, new Combining())
      } else {
       Set()
      }
    } else {
    Set()
    }
  }

  private def createRemoveContourApplications(subGoalIndex : Int,target: PrimarySpiderDiagramOccurrence): Set[PossibleRemoveContour] = {
    target.getAllContours .
      map(c => new PossibleRemoveContour(subGoalIndex,target, new RemoveContour(), c)).toSet
  }

  private def createRemoveShadedZoneApplications(subGoalIndex : Int,target: PrimarySpiderDiagramOccurrence) : Set[PossibleRemoveShadedZone] = {
    (target.getShadedZones & target.getPresentZones) .filter(z => z.getInContours.nonEmpty).
      map(z => new PossibleRemoveShadedZone(subGoalIndex, target, new RemoveShadedZone(), z)).toSet
  }

  private def createIntroducedShadedZoneApplications(subGoalIndex :Int,target: PrimarySpiderDiagramOccurrence) :Set[PossibleIntroShadedZone] = {
    (target.getShadedZones -- target.getPresentZones).
    map(z => new PossibleIntroShadedZone(subGoalIndex,target, new IntroShadedZone(), z)).toSet
  }

  private def createRemoveShadingApplications(subGoalIndex : Int,target: PrimarySpiderDiagramOccurrence): Set[PossibleRemoveShading] = {
    (target.getShadedZones & target.getPresentZones).
      map(z => new PossibleRemoveShading(subGoalIndex,target, new RemoveShading(), z)).toSet
  }

  private def createIntroduceContoursApplication(subGoalIndex : Int,target: PrimarySpiderDiagramOccurrence,
                                                 contours: java.util.Collection[String]): Set[PossibleIntroduceContour] = {
    (contours.toSet  -- target.getAllContours).
      map(c => new PossibleIntroduceContour(subGoalIndex,target, new IntroContour(), c))
  }

  // </editor-fold>

}
