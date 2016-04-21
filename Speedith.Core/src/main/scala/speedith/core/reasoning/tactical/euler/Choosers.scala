package speedith.core.reasoning.tactical.euler

import speedith.core.lang.Zone
import speedith.core.reasoning.automatic.wrappers.{PrimarySpiderDiagramOccurrence, CompoundSpiderDiagramOccurrence, SpiderDiagramOccurrence}
import scala.collection.JavaConversions._
/**
  * TODO: Description
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
