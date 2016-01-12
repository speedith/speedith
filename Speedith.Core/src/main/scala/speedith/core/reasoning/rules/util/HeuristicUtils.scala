package speedith.core.reasoning.rules.util

import java.util
import speedith.core.reasoning.{Goals, InferenceRules}
import speedith.core.reasoning.args.{RuleArg, ContourArg, MultipleRuleArgs}
import speedith.core.reasoning.rules.IntroContour

import scala.collection.JavaConversions._
import speedith.core.lang._

/**
 * Helper functions for the computation of the heuristic search. All these
 * functions assume that the given diagrams are normalised, i.e. that all zones
 * that are visible are contained in the set "presentZones". That is, the missing zones
 * are the elements of "shadedZones" that are not elements of "presentZones"
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object HeuristicUtils {

  def contourDiffMetric(d1: SpiderDiagram, d2: SpiderDiagram) : Int = {
    math.max(
      (contourM1(d2) -- contourM1(d1)).size + (contourM1(d1) -- contourM1(d2)).size,
      (contourM2(d2) -- contourM2(d1)).size + (contourM2(d1) -- contourM2(d2)).size
    )
  }

  private def  contourM1 (d: SpiderDiagram) : Set[String]  = d match {
    case d : PrimarySpiderDiagram => d.getAllContours.toSet
    case d : CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => contourM1(d.getOperand(0)) ++ contourM1(d.getOperand(1))
      case Operator.Disjunction => contourM1(d.getOperand(0)) & contourM1(d.getOperand(1))
      case Operator.Negation => contourM2(d.getOperand(0))
      case _ => new util.HashSet[String]().toSet
    }
  }

  private def  contourM2 (d: SpiderDiagram) : Set[String]  = d match {
    case d : PrimarySpiderDiagram => d.getAllContours.toSet
    case d : CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => contourM2(d.getOperand(0)) & contourM2(d.getOperand(1))
      case Operator.Disjunction => contourM2(d.getOperand(0)) ++ contourM2(d.getOperand(1))
      case Operator.Negation => contourM1(d.getOperand(0))
      case _ => new util.HashSet[String]().toSet
    }
  }

  def zoneDiffMetric(d1 :SpiderDiagram, d2: SpiderDiagram) : Int = {
    val contours = (AutomaticUtils.collectContours(d1) ++ AutomaticUtils.collectContours(d2)).toSet
    addZ(d1,d2,contours)+remZ(d1,d2,contours)
  }

  private def addZ(d1 : SpiderDiagram, d2: SpiderDiagram, contours : Set[String]) : Int = {
    math.max(
    if (zoneM1(computeCForm(d2,contours)).subsetOf(zoneM1(computeCForm(d1, contours)))) {
      0
    } else {
      1
    }
    ,
    if (zoneM2(computeCForm(d2,contours)).subsetOf(zoneM2(computeCForm(d1, contours)))) {
        0
      } else {
        1
      }
    )
  }

  private def remZ(d1 : SpiderDiagram, d2: SpiderDiagram, contours : Set[String]) : Int = {
    math.max(
      if (zoneM1(computeCForm(d1,contours)).subsetOf(zoneM1(computeCForm(d2, contours)))) {
        0
      } else {
        1
      }
      ,
      if (zoneM2(computeCForm(d1,contours)).subsetOf(zoneM2(computeCForm(d2, contours)))) {
        0
      } else {
        1
      }
    )
  }

  private def computeCForm(d1: SpiderDiagram, contours :Set[String]) : SpiderDiagram = d1 match  {
    case d1 : PrimarySpiderDiagram  =>
      val arg = createMultipleArg(contours -- d1.getAllContours)
      val rule = new IntroContour()
      val list  = new util.HashSet[SpiderDiagram]()
      val sd = SpiderDiagrams.createPrimarySD(d1.getSpiders, d1.getHabitats, d1.getShadedZones, d1.getPresentZones)
      list.add(sd)
      val goal = new Goals(list )
      if (arg.nonEmpty) {
        rule.apply(arg, goal).getGoals.getGoalAt(0)
      } else {
        sd
      }

    case d1: CompoundSpiderDiagram =>
      SpiderDiagrams.createCompoundSD(d1.getOperator.getName, d1.getOperands.map(d => computeCForm(d, contours)).toSeq)


  }

  private def createMultipleArg (contours : Set[String]) : MultipleRuleArgs = {
    new MultipleRuleArgs(contours.map(c => new ContourArg(0,0, c)).toSeq)
  }

  private def zoneM1(d: SpiderDiagram) : Set[Zone] = d match {
    case d: PrimarySpiderDiagram => d.getPresentZones.toSet
    case d: CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => zoneM1(d.getOperand(0)) & zoneM1(d.getOperand(1))
      case Operator.Disjunction => zoneM1(d.getOperand(0)) ++ zoneM1(d.getOperand(1))
      case Operator.Negation => zoneM2(d.getOperand(0))
      case _ => new util.HashSet[Zone]().toSet
    }
  }

  private def zoneM2(d: SpiderDiagram) : Set[Zone] = d match {
    case d : PrimarySpiderDiagram => d.getPresentZones.toSet
    case d : CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => zoneM2(d.getOperand(0)) & zoneM2(d.getOperand(1))
      case Operator.Disjunction => zoneM2(d.getOperand(0)) ++ zoneM2(d.getOperand(1))
      case Operator.Negation => zoneM1(d.getOperand(0))
      case _ => new util.HashSet[Zone]().toSet
    }
  }


  def shadingDiffMetric(d1 : SpiderDiagram, d2: SpiderDiagram) : Int = {
    val contours = (AutomaticUtils.collectContours(d1) ++ AutomaticUtils.collectContours(d2)).toSet
    addSh(d1,d2,contours)+remSh(d1,d2,contours)

  }

  private def addSh(d1 : SpiderDiagram, d2: SpiderDiagram, contours : Set[String]) : Int = {
    math.max(
      if (shadingM1(computeVennForm(computeCForm(d2,contours))).subsetOf(shadingM1(computeVennForm(computeCForm(d1, contours))))) {
        0
      } else {
        1
      }
      ,
      if (shadingM2(computeVennForm(computeCForm(d2,contours))).subsetOf(shadingM2(computeVennForm(computeCForm(d1, contours))))) {
        0
      } else {
        1
      }
    )
  }

  private def remSh(d1 : SpiderDiagram, d2: SpiderDiagram, contours : Set[String]) : Int = {
    math.max(
      if (shadingM1(computeVennForm(computeCForm(d1,contours))).subsetOf(shadingM1(computeVennForm(computeCForm(d2, contours))))) {
        0
      } else {
        1
      }
      ,
      if (shadingM2(computeVennForm(computeCForm(d1,contours))).subsetOf(shadingM2(computeVennForm(computeCForm(d2, contours))))) {
        0
      } else {
        1
      }
    )
  }

  private def computeVennForm(d : SpiderDiagram) : SpiderDiagram = d match {
    case d: PrimarySpiderDiagram => SpiderDiagrams.createPrimarySD(d.getSpiders, d.getHabitats, d.getShadedZones, d.getPresentZones.toSet ++d.getShadedZones).asInstanceOf[SpiderDiagram]
    case d: CompoundSpiderDiagram => SpiderDiagrams.createCompoundSD(d.getOperator.getName, d.getOperands.map(computeVennForm).toSeq)
  }

  private def shadingM1(d: SpiderDiagram) : Set[Zone] = d match {
    case d: PrimarySpiderDiagram => (d.getPresentZones & d.getShadedZones).toSet
    case d: CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => shadingM1(d.getOperand(0)) & shadingM1(d.getOperand(1))
      case Operator.Disjunction => shadingM1(d.getOperand(0)) ++ shadingM1(d.getOperand(1))
      case Operator.Negation => shadingM2(d.getOperand(0))
      case _ => new util.HashSet[Zone]().toSet
    }
  }

  private def shadingM2(d: SpiderDiagram) : Set[Zone] = d match {
    case d: PrimarySpiderDiagram => (d.getPresentZones & d.getShadedZones).toSet
    case d: CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => shadingM2(d.getOperand(0)) & shadingM2(d.getOperand(1))
      case Operator.Disjunction => shadingM2(d.getOperand(0)) ++ shadingM2(d.getOperand(1))
      case Operator.Negation => shadingM1(d.getOperand(0))
      case _ => new util.HashSet[Zone]().toSet
    }
  }


  def connectiveDiffMetric (d1 : SpiderDiagram, d2: SpiderDiagram) : Int = {
    math.max(cnnM1(d1,d2), cnnM2(d1,d2))
  }

  private def cnnM1(d1 : SpiderDiagram, d2 : SpiderDiagram) : Int = {
    val m1 = connectiveM1(d1)
    val m2 = connectiveM1(d2)
    if (m1 > 0 && m2 > 0) {
      math.abs(log2(m1) - log2(m2)).toInt
    } else if (m1 == 0 && m2 > 0 ) {
      (1 + log2(m2)).toInt
    } else if (m1 > 0 && m2 == 0) {
      (1 + log2(m1)).toInt
    } else {
      0
    }
  }

  private def cnnM2(d1 : SpiderDiagram, d2 : SpiderDiagram) : Int = {
    val m1 = connectiveM2(d1)
    val m2 = connectiveM2(d2)
    if (m1 > 0 && m2 > 0) {
      math.abs(log2(m1) - log2(m2)).toInt
    } else if (m1 == 0 && m2 > 0 ) {
      (1 + log2(m2)).toInt
    } else if (m1 > 0 && m2 == 0) {
      (1 + log2(m1)).toInt
    } else {
      0
    }
  }

  private def connectiveM1(d : SpiderDiagram): Int= d match  {
    case d : PrimarySpiderDiagram => 0
    case d: CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => d.getOperand(0) match {
        case d1 : PrimarySpiderDiagram => 1 + connectiveM1(d.getOperand(1))
        case d1 : CompoundSpiderDiagram => math.max(connectiveM1(d.getOperand(0)), connectiveM1(d.getOperand(1)))
      }
      case Operator.Disjunction => math.min(connectiveM1(d.getOperand(0)), connectiveM1(d.getOperand(1)))
      case Operator.Negation => connectiveM2(d.getOperand(0))
    }
  }

  private def connectiveM2(d : SpiderDiagram): Int= d match  {
    case d : PrimarySpiderDiagram => 0
    case d: CompoundSpiderDiagram => d.getOperator match {
      case Operator.Conjunction => d.getOperand(0) match {
        case d1 : PrimarySpiderDiagram => 1 + connectiveM2(d.getOperand(1))
        case d1 : CompoundSpiderDiagram => math.max(connectiveM2(d.getOperand(0)), connectiveM2(d.getOperand(1)))
      }
      case Operator.Disjunction => math.min(connectiveM2(d.getOperand(0)), connectiveM2(d.getOperand(1)))
      case Operator.Negation => connectiveM1(d.getOperand(0))
    }
  }


  private def log2(x : Int) = scala.math.log(x)/scala.math.log(2)
  }
