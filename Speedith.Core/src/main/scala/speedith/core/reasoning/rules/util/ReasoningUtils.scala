package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang._
import speedith.core.reasoning.Goals
import scala.collection.JavaConversions._
/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object ReasoningUtils {

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


  def expand(zones: Set[Zone], newContours: util.Set[String]) : Set[Zone] = {
    zones.flatMap(z => newContours.subsets.
      flatMap(cs => new util.HashSet[Zone]() + new Zone(z.getInContours.toSet ++ cs,z.getOutContours.toSet ++newContours.diff(cs))
      )

    )
  }


  def expand(zone :Zone, newContours : util.Set[String]) : Set[Zone] = {
    newContours.subsets.flatMap(cs => new util.HashSet[Zone]() +
      new Zone(zone.getInContours.toSet ++ cs,zone.getOutContours.toSet ++ newContours.diff(cs))).toSet
  }

  /**
   * Checks whether the given SpiderDiagram consists of exactly one implication, where
   * both the premise and the conclusion are conjunctive diagrams, i.e., either
   * primary spider diagrams or a conjunction.
   * @param goal The SpiderDiagram that will be analysed
   * @return true if goal is of the described form, false otherwise
   */
  def isImplicationOfConjunctions(goal: SpiderDiagram): Boolean = goal match {
    case goal : CompoundSpiderDiagram => goal.getOperator match {
      case  Operator.Implication  => {
        val premise: SpiderDiagram = goal.getOperand(0)
        val conclusion: SpiderDiagram = goal.getOperand(1)
        AutomaticUtils.isConjunctive(premise) && AutomaticUtils.isConjunctive(conclusion)
      }
      case _ => false
    }
    case _ => false
  }

}
