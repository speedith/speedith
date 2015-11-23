package speedith.core.reasoning.rules.util

import java.text.Collator
import java.util
import speedith.core.lang.{SpiderDiagram, PrimarySpiderDiagram, CompoundSpiderDiagram, Operator, Zone,SpiderDiagrams,Zones}
import speedith.core.reasoning.{Goals, InferenceRule}
import speedith.core.reasoning.args.RuleArg
import speedith.core.reasoning.automatic._
import speedith.core.reasoning.automatic.wrappers.{CompoundSpiderDiagramWrapper, PrimarySpiderDiagramWrapper, SpiderDiagramWrapper}
import speedith.core.reasoning.rules._

import scala.collection.GenTraversableOnce
import scala.collection.JavaConversions._
import scala.collection.JavaConverters._

/**
 * Created by sl542 on 12/11/15.
 */
object AutomaticUtils {
  def collectContours  (spiderDiagram: SpiderDiagram) : util.Collection[String] = spiderDiagram  match {
    case spiderDiagram : PrimarySpiderDiagram => spiderDiagram.getAllContours
    case spiderDiagram: CompoundSpiderDiagram => spiderDiagram.getOperands.flatMap(collectContours)
  }

  def createConjunctionEliminationApplication(target: CompoundSpiderDiagramWrapper) : util.Collection[ PossibleRuleApplication] = target.getCompoundDiagram.getOperator match  {
    case Operator.Conjunction  => new util.HashSet[PossibleRuleApplication]() + new PossibleConjunctionElimination(target, new ConjunctionElimination().asInstanceOf[InferenceRule[RuleArg]]);
    case _ => new util.HashSet[PossibleRuleApplication]();
  }

  def createCopyContourApplication(target: CompoundSpiderDiagramWrapper, applied: AppliedRules) : util.Collection[PossibleRuleApplication] = {
    if (target.getOperands.forall(o => o.isInstanceOf[PrimarySpiderDiagramWrapper])) {
      val leftContours= target.getOperand(0).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val rightContours = target.getOperand(1).asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours
      val difference =  leftContours -- rightContours
      val removed = difference -- applied.getCopiedContours(target)
      (( leftContours -- rightContours) -- applied.getCopiedContours(target))
          .map(c => new PossibleCopyContourApplication(target.getOperand(0), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c)) ++
        ((rightContours --
          leftContours) -- applied.getCopiedContours(target))
          .map(c => new PossibleCopyContourApplication(target.getOperand(1), new CopyContours().asInstanceOf[InferenceRule[RuleArg]], c))
    } else {
      new util.HashSet[PossibleRuleApplication]()
    }
  }

  def createAllPossibleRuleApplications (target: SpiderDiagramWrapper, contours: util.Collection[String], applied: AppliedRules ): util.Collection[PossibleRuleApplication] = target match {
    case target : PrimarySpiderDiagramWrapper => createRemoveContourApplications(target, applied) ++ createRemoveShadingApplications(target, applied) ++ createIntroduceContoursApplication(target, contours, applied)
    case target : CompoundSpiderDiagramWrapper =>  target.getCompoundDiagram.getOperator match  {
      case Operator.Conjunction =>  createCopyContourApplication(target, applied)++  target.getOperands.flatMap(o =>    createAllPossibleRuleApplications(o, contours, applied)) ++createConjunctionEliminationApplication(target)
      case Operator.Implication => createAllPossibleRuleApplications(target.getOperand(0), contours, applied)
      case _ => new util.HashSet[PossibleRuleApplication]()
  }
    case _ => new util.HashSet[PossibleRuleApplication]() //TODO: full implementation for Compound Diagrams!
  }


  def isConjunctive(sd : SpiderDiagram) : Boolean =  sd match {
    case sd : PrimarySpiderDiagram => true
    case sd : CompoundSpiderDiagram => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  private def createRemoveContourApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): util.Collection[PossibleRuleApplication] = {
    (target.getAllContours -- applied.getRemovedContours(target)).map(c => new PossibleRemoveContourApplication(target, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }

  private def createRemoveShadingApplications(target: PrimarySpiderDiagramWrapper, applied: AppliedRules): util.Collection[PossibleRuleApplication] = {
    ((target.getShadedZones & target.getPresentZones) -- applied.getRemovedShading(target)) .map(z => new PossibleRemoveShadingApplication(target, new RemoveShading().asInstanceOf[InferenceRule[RuleArg]], z))
  }

  private def createIntroduceContoursApplication(target: PrimarySpiderDiagramWrapper, contours: util.Collection[String], applied : AppliedRules): util.Collection[PossibleRuleApplication] = {
    ((contours.toSet -- applied.getIntroducedContours(target)) -- target.getAllContours).map(c => new PossibleIntroduceContourApplication(target, new IntroContour().asInstanceOf[InferenceRule[RuleArg]], c))
  }

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
