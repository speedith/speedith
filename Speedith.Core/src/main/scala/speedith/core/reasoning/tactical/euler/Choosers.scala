package speedith.core.reasoning.tactical.euler

import speedith.core.lang.Zone
import speedith.core.reasoning.automatic.wrappers.{PrimarySpiderDiagramOccurrence, CompoundSpiderDiagramOccurrence, SpiderDiagramOccurrence}
import speedith.core.reasoning.tactical.Chooser
import scala.collection.JavaConversions._
/**
  * Chooser functions to select arguments for single rule tactics within a diagram
  * selected by a Predicate function (see [[RuleTactics]])
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object Choosers {

  /*
      Contour choosers. Always choose a set of contours, since introducing/removing contours
      works on sets of contours.
   */

  def someInDiagramAndInGivenContours : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd : CompoundSpiderDiagramOccurrence => None
    case sd : PrimarySpiderDiagramOccurrence =>
      (sd.getAllContours & contours).headOption match {
        case None => None
        case Some(c) => Some(Set(c))
      }
  }

  def allInDiagramAndInGivenContours : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd : CompoundSpiderDiagramOccurrence => None
    case sd : PrimarySpiderDiagramOccurrence =>
      val result = (sd.getAllContours & contours).toSet
      result.isEmpty match {
        case true => None
        case _ => Some(result)
      }
  }

  def someInDiagramButNotInGivenContours : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
        (sd.getAllContours -- contours).headOption match {
          case None => None
          case Some(c) => Some(Set(c))
        }
  }

  def allInDiagramButNotInGivenContours : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val result = (sd.getAllContours -- contours).toSet
      result.isEmpty match {
        case true => None
        case _ => Some(result)
      }
  }

  def someGivenContoursButNotInDiagram : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (contours -- sd.getAllContours  ).headOption match {
        case None => None
        case Some(c) => Some(Set(c))
      }
  }

  def allInGivenContoursButNotInDiagram : Set[String] => Chooser[Set[String]] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val result = contours -- sd.getAllContours
      result.isEmpty match {
        case true => None
        case _ => Some(result)
      }
  }

  def anyContour : Chooser[Set[String]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      sd.getAllContours.headOption match {
        case None => None
        case Some(c) => Some(Set(c))
      }
  }

  /*
     Zone Choosers
   */

  def someVisibleShadedZoneNotInGivenZones : Set[Zone] => Chooser[Set[Zone]] = (zones : Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
       ((sd.getPresentZones & sd.getShadedZones) -- zones).headOption match{
         case None => None
         case Some(z) => Some(Set(z))
       }
  }

  def allVisibleShadedZoneNotInGivenZones : Set[Zone] => Chooser[Set[Zone]] = (zones : Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      val result = (sd.getPresentZones & sd.getShadedZones) -- zones
      result.isEmpty match{
        case true => None
        case _ => Some(result.toSet)
      }
  }

  def someVisibleShadedZonesInGivenZones : Set[Zone] => Chooser[Set[Zone]] = (zones:Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      ((sd.getPresentZones & sd.getShadedZones) & zones).headOption match {
        case None => None
        case Some(z) => Some(Set(z))
      }
  }

  def allVisibleShadedZonesInGivenZones : Set[Zone] => Chooser[Set[Zone]] = (zones:Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      val result = (sd.getPresentZones & sd.getShadedZones) & zones
      result.isEmpty match {
        case true => None
        case _ => Some(result.toSet)
      }
  }

  def someShadedZone : Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (sd.getPresentZones & sd.getShadedZones).headOption match {
        case None => None
        case Some(z) => z.getInContoursCount match {
          case 0 => None
          case _ => Some (Set (z) )
        }
      }
  }

  def allShadedZones : Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val result = sd.getPresentZones & sd.getShadedZones
      result.isEmpty match {
        case true => None
        case _ => Some(result.toSet)
      }
  }

  def someMissingZoneInGivenZones: Set[Zone] => Chooser[Set[Zone]] = (zones : Set[Zone]) =>  {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      (( sd.getShadedZones -- sd.getPresentZones) & zones).headOption match {
        case None => None
        case Some(z) => Some(Set(z))
      }

  }

  def allMissingZonesInGivenZones: Set[Zone] => Chooser[Set[Zone]] = (zones : Set[Zone]) =>  {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      val result = (sd.getShadedZones -- sd.getPresentZones) & zones
      result.isEmpty match {
        case true => None
        case _ => Some(result.toSet)
      }

  }

  def someMissingZone : Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (sd.getShadedZones -- sd.getPresentZones).headOption match {
        case None => None
        case Some(z) => Some(Set(z))
      }
  }

  def allMissingZonesContainingOneContour : Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val missing = (sd.getShadedZones -- sd.getPresentZones).toSet
      val contours = sd.getAllContours
      val contoursWithMissingZones= contours.filter(c => missing.exists(z => z.getInContours.contains(c)))
      contoursWithMissingZones.headOption match {
        case None => None
        case Some(c) => Some(missing.filter(_.getInContours.contains(c)))
      }
  }

  def allShadedZonesContainingOneContour: Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val shaded = (sd.getShadedZones & sd.getPresentZones).toSet
      val habitats = sd.getHabitats flatMap ( entry => entry._2.zones )
      val contours = sd.getAllContours
      val contoursWithshadedZones= contours filter (c => shaded.exists(_.getInContours.contains(c)))
      contoursWithshadedZones.headOption match {
        case None => None
        case Some(c) => Some((shaded filter (_.getInContours.contains(c))) -- habitats)
      }
  }

  def allMissingZones : Chooser[Set[Zone]] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      val result = sd.getShadedZones -- sd.getPresentZones
      result.isEmpty match {
        case true => None
        case _ => Some(result.toSet)
      }
  }

}
