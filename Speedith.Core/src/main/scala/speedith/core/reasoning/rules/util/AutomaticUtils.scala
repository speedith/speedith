package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang.{CompoundSpiderDiagram, Operator, PrimarySpiderDiagram, Region, SpiderDiagram, Zone}
import speedith.core.reasoning.InferenceRule
import speedith.core.reasoning.args.RuleArg
import speedith.core.reasoning.automatic.rules._
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramOccurrence, PrimarySpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.rules._
import speedith.core.reasoning.util.unitary.CorrespondingRegions

import scala.collection.JavaConversions._

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
  def createAllPossibleRuleApplications (target: SpiderDiagramOccurrence, contours: util.Collection[String]): util.Set[PossibleRuleApplication] = target match {
    case target : PrimarySpiderDiagramOccurrence =>
      createRemoveShadedZoneApplications(target) ++
        createRemoveShadingApplications(target) ++
        createIntroducedShadedZoneApplications(target) ++
        createRemoveContourApplications(target) ++
        createIntroduceContoursApplication(target, contours) ++
        new java.util.HashSet[PossibleRuleApplication]()
    case target : CompoundSpiderDiagramOccurrence =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>
        createCopyContourApplications(target) ++
          createCopyShadingApplications(target) ++
          createCombiningApplications(target) ++
          target.getOperands.flatMap(createAllPossibleRuleApplications(_, contours)) ++
          createConjunctionEliminationApplication(target)
      case Operator.Implication => createAllPossibleRuleApplications(target.getOperand(0), contours)
      case _ => new java.util.HashSet[PossibleRuleApplication]()
    }
    case _ => new java.util.HashSet[PossibleRuleApplication]() //TODO: full implementation for Compound Diagrams!
  }

  private def createConjunctionEliminationApplication(target: CompoundSpiderDiagramOccurrence) : java.util.Collection[ PossibleRuleApplication] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => new java.util.HashSet[PossibleRuleApplication]() +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(0)) +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(1))
    case _ => new java.util.HashSet[PossibleRuleApplication]();
  }

  private def createCopyContourApplications(target: CompoundSpiderDiagramOccurrence) : java.util.Set[PossibleRuleApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
      val difference =  leftContours -- rightContours
      ( leftContours -- rightContours)
          .map(c => new PossibleCopyContourApplication(target.getOperand(0), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication]) ++
        (rightContours -- leftContours)
          .map(c => new PossibleCopyContourApplication(target.getOperand(1), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication])
    } else {
      new java.util.HashSet[PossibleRuleApplication]()
    }
  }

  private def createCopyShadingApplications(target: CompoundSpiderDiagramOccurrence) : util.Set[PossibleCopyShadingApplication] = {
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
              map(r => new PossibleCopyShadingApplication(target.getOperand(0), new CopyShading().asInstanceOf[InferenceRule[RuleArg]], r._1))
        val rightShadedRegions = (rightDiagram.getShadedZones & rightDiagram.getPresentZones)
          .subsets.toSet.filter(r => r.nonEmpty)
        val rightRegions = rightShadedRegions.
          map(r => Tuple2(r, CorrespondingRegions(rightDiagram, leftDiagram).correspondingRegion(new Region(r)))).filter(t => t._2.zones.nonEmpty)
        val rightResult = rightRegions.
          map(r => new PossibleCopyShadingApplication(target.getOperand(1), new CopyShading().asInstanceOf[InferenceRule[RuleArg]], r._1))
        leftResult ++ rightResult
      }
      else {
        new util.HashSet[PossibleCopyShadingApplication]()
      }
    } else {
      new util.HashSet[PossibleCopyShadingApplication]()
    }
  }

  private def createCombiningApplications(target: CompoundSpiderDiagramOccurrence) : java.util.Set[PossibleCombiningApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramOccurrence])) {
      val leftZones = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      val rightZones = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      if (leftZones.equals(rightZones)) {
        new java.util.HashSet[PossibleCombiningApplication]() + new PossibleCombiningApplication(target, new Combining().asInstanceOf[InferenceRule[RuleArg]])
      } else {
        new java.util.HashSet[PossibleCombiningApplication]()
      }
    } else {
    new java.util.HashSet[PossibleCombiningApplication]()
    }
  }

  private def createRemoveContourApplications(target: PrimarySpiderDiagramOccurrence): java.util.Set[PossibleRemoveContourApplication] = {
    target.getAllContours .
      map(c => new PossibleRemoveContourApplication(target, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }

  private def createRemoveShadedZoneApplications(target: PrimarySpiderDiagramOccurrence) : java.util.Set[PossibleRuleApplication] = {
    (target.getShadedZones & target.getPresentZones) .
      map(z => new PossibleRemoveShadedZoneApplication(target, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroducedShadedZoneApplications(target: PrimarySpiderDiagramOccurrence) : java.util.Set[PossibleIntroShadedZoneApplication] = {
    (target.getShadedZones -- target.getPresentZones).
    map(z => new PossibleIntroShadedZoneApplication(target, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]], z))
  }

  private def createRemoveShadingApplications(target: PrimarySpiderDiagramOccurrence): java.util.Set[PossibleRuleApplication] = {
    (target.getShadedZones & target.getPresentZones).
      map(z => new PossibleRemoveShadingApplication(target, new RemoveShading().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroduceContoursApplication(target: PrimarySpiderDiagramOccurrence,
                                                 contours: java.util.Collection[String]): java.util.Set[PossibleIntroduceContourApplication] = {
    (contours.toSet  -- target.getAllContours).
      map(c => new PossibleIntroduceContourApplication(target, new IntroContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }

  // </editor-fold>

}
