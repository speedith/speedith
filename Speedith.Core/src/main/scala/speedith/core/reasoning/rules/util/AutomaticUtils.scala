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
   * @param target The SpiderDiagramOccurrence for which the set of PossibleRuleApplication will be created
   * @param contours The set of contours present in the whole subgoal target is contained in
   * @return A set of PossibleRuleApplication denoting all rule applications possible to target
   */
  def createAllPossibleRuleApplications(target: SpiderDiagramOccurrence, contours: util.Collection[String]):java.util.Set[_ <: PossibleRuleApplication[_ <: RuleArg]]  = {
   createAllPossibleRuleApplicationsRec(target, contours)
  }


  private def createAllPossibleRuleApplicationsRec (target: SpiderDiagramOccurrence, contours: util.Collection[String]):Set[_ <: PossibleRuleApplication[_ <: RuleArg]] = target match {
    case target : PrimarySpiderDiagramOccurrence =>
      createRemoveShadedZoneApplications(target) ++
        createRemoveShadingApplications(target) ++
        createIntroducedShadedZoneApplications(target) ++
        createRemoveContourApplications(target) ++
        createIntroduceContoursApplication(target, contours)
    case target : CompoundSpiderDiagramOccurrence =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>
        createCopyContourApplications(target) ++
          createCopyShadingApplications(target) ++
          createCombiningApplications(target) ++
          createAllPossibleRuleApplicationsRec(target.getOperand(0), contours) ++
          createAllPossibleRuleApplicationsRec(target.getOperand(1), contours) ++
          createConjunctionEliminationApplication(target)
      case Operator.Implication => createAllPossibleRuleApplicationsRec(target.getOperand(0), contours)
      case _ => Set()
    }
    case _ => Set() //TODO: full implementation for Compound Diagrams!
  }



  private def createConjunctionEliminationApplication(target: CompoundSpiderDiagramOccurrence) : Set[PossibleConjunctionElimination] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => Set() +
      new PossibleConjunctionElimination(target, new ConjunctionElimination(), target.getOperand(0)) +
      new PossibleConjunctionElimination(target, new ConjunctionElimination(), target.getOperand(1))
    case _ => Set();
  }

  private def createCopyContourApplications(target: CompoundSpiderDiagramOccurrence) : Set[PossibleCopyContourApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val difference =  leftContours -- rightContours
      (( leftContours -- rightContours)
          .map(c => new PossibleCopyContourApplication(target.getOperand(0), new CopyContoursTopological(), c)) ++
        (rightContours -- leftContours)
          .map(c => new PossibleCopyContourApplication(target.getOperand(1), new CopyContoursTopological(), c))).toSet
    } else {
      Set()
    }
  }

  private def createCopyShadingApplications(target: CompoundSpiderDiagramOccurrence) : Set[PossibleCopyShadingApplication] = {
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
              map(r => new PossibleCopyShadingApplication(target.getOperand(0), new CopyShading(), r._1))
        val rightShadedRegions = (rightDiagram.getShadedZones & rightDiagram.getPresentZones)
          .subsets.toSet.filter(r => r.nonEmpty)
        val rightRegions = rightShadedRegions.
          map(r => Tuple2(r, CorrespondingRegions(rightDiagram, leftDiagram).correspondingRegion(new Region(r)))).filter(t => t._2.zones.nonEmpty)
        val rightResult = rightRegions.
          map(r => new PossibleCopyShadingApplication(target.getOperand(1), new CopyShading(), r._1))
        leftResult ++ rightResult
      }
      else {
        Set()
      }
    } else {
      Set()
    }
  }

  private def createCombiningApplications(target: CompoundSpiderDiagramOccurrence) : Set[PossibleCombiningApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftZones = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      val rightZones = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      if (leftZones.equals(rightZones)) {
        Set() + new PossibleCombiningApplication(target, new Combining())
      } else {
       Set()
      }
    } else {
    Set()
    }
  }

  private def createRemoveContourApplications(target: PrimarySpiderDiagramOccurrence): Set[PossibleRemoveContourApplication] = {
    target.getAllContours .
      map(c => new PossibleRemoveContourApplication(target, new RemoveContour(), c)).toSet
  }

  private def createRemoveShadedZoneApplications(target: PrimarySpiderDiagramOccurrence) : Set[PossibleRemoveShadedZoneApplication] = {
    (target.getShadedZones & target.getPresentZones) .filter(z => z.getInContours.nonEmpty).
      map(z => new PossibleRemoveShadedZoneApplication(target, new RemoveShadedZone(), z)).toSet
  }

  private def createIntroducedShadedZoneApplications(target: PrimarySpiderDiagramOccurrence) :Set[PossibleIntroShadedZoneApplication] = {
    (target.getShadedZones -- target.getPresentZones).
    map(z => new PossibleIntroShadedZoneApplication(target, new IntroShadedZone(), z)).toSet
  }

  private def createRemoveShadingApplications(target: PrimarySpiderDiagramOccurrence): Set[PossibleRemoveShadingApplication] = {
    (target.getShadedZones & target.getPresentZones).
      map(z => new PossibleRemoveShadingApplication(target, new RemoveShading(), z)).toSet
  }

  private def createIntroduceContoursApplication(target: PrimarySpiderDiagramOccurrence,
                                                 contours: java.util.Collection[String]): Set[PossibleIntroduceContourApplication] = {
    (contours.toSet  -- target.getAllContours).
      map(c => new PossibleIntroduceContourApplication(target, new IntroContour(), c))
  }

  // </editor-fold>

}
