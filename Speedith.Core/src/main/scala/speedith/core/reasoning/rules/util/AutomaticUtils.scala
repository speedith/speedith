package speedith.core.reasoning.rules.util

import java.util
import speedith.core.lang.{SpiderDiagram, PrimarySpiderDiagram, CompoundSpiderDiagram, Operator, Zone,SpiderDiagrams,Zones}
import speedith.core.reasoning.automatic.rules._
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
  def collectContours  (spiderDiagram: SpiderDiagram) : util.Collection[String] = spiderDiagram  match {
    case spiderDiagram : PrimarySpiderDiagram => spiderDiagram.getAllContours
    case spiderDiagram: CompoundSpiderDiagram => spiderDiagram.getOperands.flatMap(collectContours)
  }

  def createConjunctionEliminationApplication(target: CompoundSpiderDiagramWrapper) : util.Collection[ PossibleRuleApplication] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => new util.HashSet[PossibleRuleApplication]() +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(0)) +
      new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]], target.getOperand(1))
    case _ => new util.HashSet[PossibleRuleApplication]();
  }

  def createCopyContourApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleRuleApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val difference =  leftContours -- rightContours
      val removed = difference -- applied.getCopiedContours(target)
      (( leftContours -- rightContours) -- applied.getCopiedContours(target))
          .map(c => new PossibleCopyContourApplication(target.getOperand(0), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication]) ++
        ((rightContours --
          leftContours) -- applied.getCopiedContours(target))
          .map(c => new PossibleCopyContourApplication(target.getOperand(1), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication])
    } else {
      new util.HashSet[PossibleRuleApplication]()
    }
  }

  def createCopyShadingApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleCopyShadingApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      if (leftContours.equals(rightContours)) {
        val leftShadedRegions = (target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getShadedZones &
          target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones).
          subsets.filter(r => r.nonEmpty).toSet
        val rightShadedRegions = (target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getShadedZones &
          target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones)
          .subsets.filter(r => r.nonEmpty).toSet
        leftShadedRegions.
          filter(r => !applied.getCopiedShadings(target.getOperand(0)).contains(r)).
          diff(rightShadedRegions).
          map(r => new PossibleCopyShadingApplication(target.getOperand(0), new CopyShading().asInstanceOf[InferenceRule[RuleArg]], r)) ++
        rightShadedRegions.
          filter(r => !applied.getCopiedShadings(target.getOperand(1)).contains(r)).
          diff(leftShadedRegions).
          map(r => new PossibleCopyShadingApplication(target.getOperand(1), new CopyShading().asInstanceOf[InferenceRule[RuleArg]], r))
      } else {
        new util.HashSet[PossibleCopyShadingApplication]()
      }
    } else {
      new util.HashSet[PossibleCopyShadingApplication]()
    }

  }

  def createCombiningApplications(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleCombiningApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftZones = target.getOperand(0).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      val rightZones = target.getOperand(1).getDiagram.asInstanceOf[PrimarySpiderDiagram].getPresentZones
      if (leftZones.equals(rightZones)) {
        new util.HashSet[PossibleCombiningApplication]() + new PossibleCombiningApplication(target, new Combining().asInstanceOf[InferenceRule[RuleArg]])
      } else {
        new util.HashSet[PossibleCombiningApplication]()
      }
    } else {
    new util.HashSet[PossibleCombiningApplication]()
    }
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
          createIntroduceContoursApplication(target, contours, applied)
    case target : CompoundSpiderDiagramWrapper =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>
            createCopyContourApplications(target, applied) ++
            createCopyShadingApplications(target,applied) ++
            createCombiningApplications(target, applied) ++
            target.getOperands.flatMap(o => createAllPossibleRuleApplications(o, contours, applied)) ++
            createConjunctionEliminationApplication(target)
      case Operator.Implication => createAllPossibleRuleApplications(target.getOperand(0), contours, applied)
      case _ => new util.HashSet[PossibleRuleApplication]()
  }
    case _ => new util.HashSet[PossibleRuleApplication]() //TODO: full implementation for Compound Diagrams!
  }


  def isConjunctive(sd : SpiderDiagram) : Boolean =  sd match {
    case sd : PrimarySpiderDiagram => true
    case sd : CompoundSpiderDiagram => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  private def createRemoveContourApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): util.Set[PossibleRuleApplication] = {
    (target.getAllContours -- applied.getRemovedContours(target)).
      map(c => new PossibleRemoveContourApplication(target, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication])
  }

  private def createRemoveShadedZoneApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleRuleApplication] = {
    ((target.getShadedZones & target.getPresentZones) -- applied.getRemovedShadedZones(target)) .
      map(z => new PossibleRemoveShadedZoneApplication(target, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroducedShadedZoneApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules) : util.Set[PossibleIntroShadedZoneApplication] = {
    ((target.getShadedZones -- target.getPresentZones) -- applied.getIntroducedShadedZones(target)).
    map(z => new PossibleIntroShadedZoneApplication(target, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]], z))
  }

  private def createRemoveShadingApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): util.Set[PossibleRuleApplication] = {
    ((target.getShadedZones & target.getPresentZones) -- applied.getRemovedShading(target)).
      map(z => new PossibleRemoveShadingApplication(target, new RemoveShading().asInstanceOf[InferenceRule[RuleArg]], z).asInstanceOf[PossibleRuleApplication])
  }

  private def createIntroduceContoursApplication(target: PrimarySpiderDiagramWrapper,
                                                 contours: util.Collection[String],
                                                 applied : AppliedRules): util.Set[PossibleRuleApplication] = {
    ((contours.toSet -- applied.getIntroducedContours(target)) -- target.getAllContours).
      map(c => new PossibleIntroduceContourApplication(target, new IntroContour().asInstanceOf[InferenceRule[RuleArg]], c).asInstanceOf[PossibleRuleApplication])
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
      SpiderDiagrams.createCompoundSD(csd.getOperator, new util.ArrayList[SpiderDiagram](csd.getOperands.map(o=>  normalize(o))), true)
    }
  }

}
