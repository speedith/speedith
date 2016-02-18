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

  def firstOfTheGivenContours : Set[String] => Chooser[String] = (contours : Set[String]) => {
    case sd : CompoundSpiderDiagramOccurrence => None
    case sd : PrimarySpiderDiagramOccurrence => try {
      Some((sd.getAllContours & contours).head)
    }
    catch {
      case e: Exception => None
    }
  }

  def firstOfTheOtherContours : Set[String] => Chooser[String] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      try {
        Some((sd.getAllContours -- contours).head)
      } catch {
        case e: Exception => None
      }
  }

  def firstVisibleShadedZoneNotInGivenZones : Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      try {
        Some(((sd.getPresentZones & sd.getShadedZones) -- zones).head)
      }
      catch {
        case e: Exception=> None
      }
  }

  def someVisibleShadedZonesInGivenZones : Set[Zone] => Chooser[Zone] = (zones:Set[Zone]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence => ((sd.getPresentZones & sd.getShadedZones) & zones).headOption
  }

  def anyShadedZone : Chooser[Zone] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      try {
        Some((sd.getPresentZones & sd.getShadedZones).head)
      }
      catch {
        case e: Exception => None
      }
  }

  def firstMissingZoneInGivenZones: Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) =>  {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence => try {
      Some((( sd.getShadedZones -- sd.getPresentZones) & zones).head)
    }
    catch {
      case e: Exception => None
    }
  }

  def anyMissingZone : Chooser[Zone] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      try {
        Some((sd.getShadedZones -- sd.getPresentZones).head)
      }
      catch {
        case e: Exception => None
      }
  }

  def anyContour : Chooser[String] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      try {
        Some(sd.getAllContours.head)
      }
      catch {
        case e: Exception => None
      }
  }


}
