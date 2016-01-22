package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang.{SpiderDiagram, PrimarySpiderDiagram, CompoundSpiderDiagram, Operator, Zones, Zone, SpiderDiagrams, Region}
import speedith.core.reasoning.automatic.rules._
import speedith.core.reasoning.util.unitary.CorrespondingRegions
import speedith.core.reasoning.{Goals, InferenceRule}
import speedith.core.reasoning.args.RuleArg
import speedith.core.reasoning.automatic._
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramWrapper, PrimarySpiderDiagramWrapper, SpiderDiagramWrapper}
import speedith.core.reasoning.rules._

import scala.collection.JavaConversions._

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
object AutomaticUtils {
  def collectContours  (spiderDiagram: SpiderDiagram) : java.util.Collection[String] = spiderDiagram  match {
    case spiderDiagram : PrimarySpiderDiagram => spiderDiagram.getAllContours
    case spiderDiagram: CompoundSpiderDiagram => spiderDiagram.getOperands.flatMap(collectContours)
  }

  def isConjunctive(sd : SpiderDiagram) : Boolean =  sd match {
    case sd : PrimarySpiderDiagram => true
    case sd : CompoundSpiderDiagram => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  /**
   * Creates all zones to the set of present zones which are normally implicitly inferred for each subgoal
   *
   * Adds zones to the set of present zones in each subgoal. The added zones are taken from all
   * possible zones, without the shaded zones that are not in the set of currently present zones (i.e., that are
   * are missing zones, in the typical definition of Spider Diagrams).
   * @param goals The set of goals to be normalised
   * @return
   */
  def normalize (goals : Goals) : Goals = new Goals(normalize(goals.getGoals))

  def normalize (sds : java.util.Collection[SpiderDiagram]) : java.util.Collection[SpiderDiagram] = sds.map(o => normalize(o))

  def normalize (sd : SpiderDiagram): SpiderDiagram= sd match {
    case psd: PrimarySpiderDiagram => {
      val possibleZones: Set[Zone] = Zones.allZonesForContours(psd.getAllContours.toSeq: _*).toSet
      SpiderDiagrams.createPrimarySD(psd.getSpiders, psd.getHabitats, psd.getShadedZones, possibleZones -- (psd.getShadedZones -- psd.getPresentZones))
    }
    case csd : CompoundSpiderDiagram => {
      SpiderDiagrams.createCompoundSD(csd.getOperator, new java.util.ArrayList[SpiderDiagram](csd.getOperands.map(o=>  normalize(o))), true)
    }
  }

  def regionWithNewContours(region: Iterable[Zone], contoursToAdd: Set[String] ): Set[Zone] = {
    region.map(zone => new Zone(zone.getInContours ++ contoursToAdd, zone.getOutContours )).toSet ++ region.map(zone => new Zone(zone.getInContours , zone.getOutContours ++ contoursToAdd )).toSet
  }

  def expand(zones: Set[Zone], contoursOnlyInSource: util.Set[String]) : Set[Zone] = {
    zones.flatMap(z => contoursOnlyInSource.subsets.
      flatMap(cs => new util.HashSet[Zone]() + new Zone(z.getInContours.toSet ++ cs,z.getOutContours.toSet ++contoursOnlyInSource.diff(cs))
      )

    )
  }
  def expand(zone :Zone, contoursOnlyInSource : util.Set[String]) : Set[Zone] = {
    contoursOnlyInSource.subsets.flatMap(cs => new util.HashSet[Zone]() +
      new Zone(zone.getInContours.toSet ++ cs,zone.getOutContours.toSet ++contoursOnlyInSource.diff(cs))).toSet
  }

/*  def regionCorrespond(source: PrimarySpiderDiagram, target: PrimarySpiderDiagram, sourceRegion: Set[Zone], targetRegion: Set[Zone]): Boolean = {
    val contoursOnlyInSource = source.getAllContours -- target.getAllContours
    val contoursOnlyInTarget = target.getAllContours -- source.getAllContours
    // compute the expansions of the missing zones in source and target
    val sourceDiagramMZExpansion = AutomaticUtils.expand(source.getShadedZones.toSet -- source.getPresentZones, contoursOnlyInTarget )
    val targetDiagramMZExpansion = AutomaticUtils.expand(target.getShadedZones.toSet -- target.getPresentZones, contoursOnlyInSource )

    val sourceExpansion = sourceDiagramMZExpansion ++ targetDiagramMZExpansion ++ AutomaticUtils.expand(sourceRegion, contoursOnlyInTarget)
    val targetExpansion = targetDiagramMZExpansion ++ sourceDiagramMZExpansion ++ AutomaticUtils.expand(targetRegion, contoursOnlyInSource)
    sourceExpansion.equals(targetExpansion)
  }
  */
  def regionCorrespond (sourceRegion: Set[Zone], sourceMissingZoneExpansion : Set[Zone], contoursOnlyInSource: Set[String],
                        targetRegion: Set[Zone], targetMissingZonExpansion: Set[Zone] , contoursOnlyInTarget: Set[String]): Boolean = {
    val sourceExpansion = sourceMissingZoneExpansion ++ targetMissingZonExpansion++ AutomaticUtils.expand(sourceRegion, contoursOnlyInTarget)
    val targetExpansion = targetMissingZonExpansion ++ sourceMissingZoneExpansion ++ AutomaticUtils.expand(targetRegion, contoursOnlyInSource)
    sourceExpansion.equals(targetExpansion)

  }

  /**
   * Creates all possible rule application for the given SpiderDiagram with respect to the given set of contours and excluding
   * all elements already contained in the given set of applied rules.
   *
   * @param target The SpiderDiagramWrapper for which the set of PossibleRuleApplication will be created
   * @param contours The set of contours present in the whole subgoal target is contained in
   * @param applied The set of already applied rules
   * @return A set of PossibleRuleApplication denoting all rule applications possible to target
   */
  def createAllPossibleRuleApplications (target: SpiderDiagramWrapper, contours: util.Collection[String], applied: AppliedRules ): util.Set[PossibleRuleApplication] = target match {
    case target : PrimarySpiderDiagramWrapper =>
      createRemoveShadedZoneApplications(target, applied) ++
        createRemoveShadingApplications(target, applied) ++
        createIntroducedShadedZoneApplications(target, applied) ++
        createRemoveContourApplications(target, applied) ++
        createIntroduceContoursApplication(target, contours, applied) ++
        new java.util.HashSet[PossibleRuleApplication]()
    case target : CompoundSpiderDiagramWrapper =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>
        createCopyContourApplications(target, applied) ++
          createCopyShadingApplications(target,applied) ++
          createCombiningApplications(target, applied) ++
          target.getOperands.flatMap(o => createAllPossibleRuleApplications(o, contours, applied)) ++
          createConjunctionEliminationApplication(target)
      case Operator.Implication => createAllPossibleRuleApplications(target.getOperand(0), contours, applied)
      case _ => new java.util.HashSet[PossibleRuleApplication]()
    }
    case _ => new java.util.HashSet[PossibleRuleApplication]() //TODO: full implementation for Compound Diagrams!
  }

  private def createConjunctionEliminationApplication(target: CompoundSpiderDiagramWrapper) : java.util.Collection[ PossibleRuleApplication] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => new java.util.HashSet[PossibleRuleApplication]() +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(0)) +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(1))
    case _ => new java.util.HashSet[PossibleRuleApplication]();
  }

  private def createCopyContourApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : java.util.Set[PossibleRuleApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val difference =  leftContours -- rightContours
      val removed = difference -- applied.getCopiedContours(target.getOperand(0))
      (( leftContours -- rightContours) -- applied.getCopiedContours(target.getOperand(0)))
          .map(c => new PossibleCopyContourApplication(target.getOperand(0), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication]) ++
        ((rightContours --
          leftContours) -- applied.getCopiedContours(target.getOperand(1)))
          .map(c => new PossibleCopyContourApplication(target.getOperand(1), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication])
    } else {
      new java.util.HashSet[PossibleRuleApplication]()
    }
  }

  private def createCopyShadingApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleCopyShadingApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftDiagram = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram]
      val rightDiagram = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram]
      val leftContours= leftDiagram.getAllContours
      val rightContours = rightDiagram.getAllContours
      if (leftContours.subsetOf(rightContours) || rightContours.subsetOf(leftContours)) {
//        val contoursOnlyInLeft = leftContours -- rightContours
//        val contoursOnlyInRight = rightContours -- leftContours
        val leftVisibleShadedZones = leftDiagram.getShadedZones & leftDiagram.getPresentZones
        val leftNonEmptyShadedRegions = leftVisibleShadedZones.subsets.toSet.filter(s => s.nonEmpty)
        val leftRegionsNotYetCopied = leftNonEmptyShadedRegions.
              filter(r => !applied.getCopiedShadings(target.getOperand(0)).contains(r))
        val leftRegions = leftRegionsNotYetCopied.map(region => Tuple2(region, CorrespondingRegions(leftDiagram, rightDiagram).correspondingRegion(new Region(region)))).filter(r => r._2.zones.nonEmpty)
        val leftResult = leftRegions.
              map(r => new PossibleCopyShadingApplication(target.getOperand(0), new CopyShading().asInstanceOf[InferenceRule[RuleArg]], r._1)).toSet
        val rightShadedRegions = (rightDiagram.getShadedZones & rightDiagram.getPresentZones)
          .subsets.toSet.filter(r => r.nonEmpty).toSet
        val rightNotYetCopied = rightShadedRegions.
          filter(r => !applied.getCopiedShadings(target.getOperand(1)).contains(r))
        val rightRegions = rightNotYetCopied.
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

  private def createCombiningApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : java.util.Set[PossibleCombiningApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
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

  private def createRemoveContourApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): java.util.Set[PossibleRemoveContourApplication] = {
    (target.getAllContours -- applied.getRemovedContours(target)).
      map(c => new PossibleRemoveContourApplication(target, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }

  private def createRemoveShadedZoneApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules) : java.util.Set[PossibleRuleApplication] = {
    ((target.getShadedZones & target.getPresentZones) -- applied.getRemovedShadedZones(target)) .
      map(z => new PossibleRemoveShadedZoneApplication(target, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroducedShadedZoneApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules) : java.util.Set[PossibleIntroShadedZoneApplication] = {
    ((target.getShadedZones -- target.getPresentZones) -- applied.getIntroducedShadedZones(target)).
    map(z => new PossibleIntroShadedZoneApplication(target, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]], z))
  }

  private def createRemoveShadingApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): java.util.Set[PossibleRuleApplication] = {
    ((target.getShadedZones & target.getPresentZones) -- applied.getRemovedShading(target)).
      map(z => new PossibleRemoveShadingApplication(target, new RemoveShading().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroduceContoursApplication(target: PrimarySpiderDiagramWrapper,
                                                 contours: java.util.Collection[String],
                                                 applied : AppliedRules): java.util.Set[PossibleIntroduceContourApplication] = {
    ((contours.toSet -- applied.getIntroducedContours(target)) -- target.getAllContours).
      map(c => new PossibleIntroduceContourApplication(target, new IntroContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }



}
