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
      val result = (contours -- sd.getAllContours).toSet
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

  def someVisibleShadedZoneNotInGivenZones : Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
       ((sd.getPresentZones & sd.getShadedZones) -- zones).headOption
  }

  def someVisibleShadedZonesInGivenZones : Set[Zone] => Chooser[Zone] = (zones:Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence => ((sd.getPresentZones & sd.getShadedZones) & zones).headOption
  }

  def anyShadedZone : Chooser[Zone] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (sd.getPresentZones & sd.getShadedZones).headOption
  }

  def someMissingZoneInGivenZones: Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) =>  {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      (( sd.getShadedZones -- sd.getPresentZones) & zones).headOption
  }

  def anyMissingZone : Chooser[Zone] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (sd.getShadedZones -- sd.getPresentZones).headOption
  }
}
