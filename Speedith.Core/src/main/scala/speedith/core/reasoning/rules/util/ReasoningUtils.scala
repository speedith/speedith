package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang._
import speedith.core.reasoning.Goals
import speedith.core.reasoning.automatic.wrappers.{PrimarySpiderDiagramOccurrence, CompoundSpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.util.unitary.CorrespondingRegions

import scala.collection.JavaConversions._
import scala.collection.JavaConverters._

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
    *
    * @param goals The set of goals to be normalised
   * @return
   */
  def normalize (goals : Goals) : Goals = new Goals(normalize(goals.getGoals))

  def normalize (sds : java.util.Collection[SpiderDiagram]) : java.util.Collection[SpiderDiagram] = sds.map(o => normalize(o))

  def normalize (sd : SpiderDiagram): SpiderDiagram= sd match {
    case psd: PrimarySpiderDiagram =>
      val allContours = psd.getAllContours.toSeq.asJava
      val possibleZones: Set[Zone] = Zones.allZonesForContours(allContours: _*).toSet
      SpiderDiagrams.createPrimarySD(psd.getSpiders, psd.getHabitats, psd.getShadedZones, possibleZones -- (psd.getShadedZones -- psd.getPresentZones))
    case csd : CompoundSpiderDiagram =>
      SpiderDiagrams.createCompoundSD(csd.getOperator, new java.util.ArrayList[SpiderDiagram](csd.getOperands.map(o=>  normalize(o))), true)
  }


  def expand(zones: Set[Zone], newContours: util.Set[String]) : Set[Zone] = {
    zones.flatMap(z => newContours.subsets.
      flatMap(cs => new util.HashSet[Zone]() + new Zone(z.getInContours.toSet ++ cs,z.getOutContours.toSet ++newContours.diff(cs))
      )

    )
  }


  def expand(zone :Zone, newContours : util.Set[String]) : Set[Zone] = {
    if (newContours.isEmpty) {
      Set(zone)
    }  else {
      newContours.subsets.flatMap(cs => new util.HashSet[Zone]() +
        new Zone(zone.getInContours.toSet ++ cs, zone.getOutContours.toSet ++ newContours.diff(cs))).toSet
    }
  }

  /**
   * Checks whether the given SpiderDiagram consists of exactly one implication, where
   * both the premise and the conclusion are conjunctive diagrams, i.e., either
   * primary spider diagrams or a conjunction.
    *
    * @param goal The SpiderDiagram that will be analysed
   * @return true if goal is of the described form, false otherwise
   */
  def isImplicationOfConjunctions(goal: SpiderDiagram): Boolean = goal match {
    case goal : CompoundSpiderDiagram => goal.getOperator match {
      case  Operator.Implication  =>
        val premise: SpiderDiagram = goal.getOperand(0)
        val conclusion: SpiderDiagram = goal.getOperand(1)
        isConjunctive(premise) && isConjunctive(conclusion)
      case _ => false
    }
    case _ => false
  }

  def isImplicationOfConjunctions(goal: SpiderDiagramOccurrence): Boolean = goal match {
    case goal : CompoundSpiderDiagramOccurrence => goal.getOperator match {
      case  Operator.Implication  =>
        val premise: SpiderDiagramOccurrence = goal.getOperand(0)
        val conclusion: SpiderDiagramOccurrence = goal.getOperand(1)
        isConjunctive(premise) && isConjunctive(conclusion)
      case _ => false
    }
    case _ => false
  }

  def isConjunctive(sd : SpiderDiagram) : Boolean =  sd match {
    case sd : PrimarySpiderDiagram => true
    case sd : CompoundSpiderDiagram => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  def isConjunctive(sd : SpiderDiagramOccurrence) : Boolean =  sd match {
    case sd : PrimarySpiderDiagramOccurrence => true
    case sd : CompoundSpiderDiagramOccurrence => sd.getOperator.equals(Operator.getConjunction) && sd.getOperands.forall(isConjunctive)
  }

  def getPrimaryDiagrams(sd: SpiderDiagram): Seq[PrimarySpiderDiagram] = sd match {
    case sd:PrimarySpiderDiagram => Seq(sd)
    case sd:CompoundSpiderDiagram => getPrimaryDiagrams(sd.getOperand(0)) ++ getPrimaryDiagrams(sd.getOperand(1))
  }

  def shadedRegionWithNewContours(region: Iterable[Zone], contoursToAdd: Set[String] ): Set[Zone] = {
    val powSetContours = contoursToAdd.subsets.toSet
    // if the region is empty, no new shaded zones will be created
    powSetContours.flatMap(c  => region.map(zone => new Zone(zone.getInContours ++ c, zone.getOutContours ++ (contoursToAdd -- c))).toSet ++ region.map(zone => new Zone(zone.getInContours ++ (contoursToAdd -- c), zone.getOutContours ++ c)))
  }

  def regionWithNewContours(region: Iterable[Zone], contoursToAdd: Set[String] ): Set[Zone] = {
    val powSetContours = contoursToAdd.subsets.toSet
    if (region.nonEmpty) {
      powSetContours.flatMap(c => region.map(zone => new Zone(zone.getInContours ++ c, zone.getOutContours ++ (contoursToAdd -- c))).toSet ++ region.map(zone => new Zone(zone.getInContours ++ (contoursToAdd -- c), zone.getOutContours ++ c)))
    } else {
      // if the region is empty, we create the new zones from scratch
      powSetContours.flatMap(c => Set(new Zone( c, contoursToAdd -- c), new Zone(contoursToAdd -- c, c)))
    }
  }

  def getCorrespondingShadedRegionInSource(source: PrimarySpiderDiagram, target:PrimarySpiderDiagram, targetRegion: Region):Region = {
    val possibleRegions = (source.getShadedZones & source.getPresentZones).subsets().toSet.filter(_.nonEmpty)
    val corr = CorrespondingRegions(source, target)
    possibleRegions.filter(testRegion => targetRegion.equals(corr.correspondingRegion(new Region(testRegion))))
    possibleRegions.headOption match {
      case Some(r) => new Region(r)
      case _ => new Region()
    }
  }

}
