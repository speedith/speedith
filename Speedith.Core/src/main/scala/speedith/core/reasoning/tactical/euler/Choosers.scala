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
    case sd : PrimarySpiderDiagramOccurrence => (sd.getAllContours & contours).headOption
  }

  def firstOfTheOtherContours : Set[String] => Chooser[String] = (contours : Set[String]) => {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
        (sd.getAllContours -- contours).headOption
  }

  def firstVisibleShadedZoneNotInGivenZones : Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) => {
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

  def firstMissingZoneInGivenZones: Set[Zone] => Chooser[Zone] = (zones : Set[Zone]) =>  {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd:PrimarySpiderDiagramOccurrence =>
      (( sd.getShadedZones -- sd.getPresentZones) & zones).headOption
  }

  def anyMissingZone : Chooser[Zone] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      (sd.getShadedZones -- sd.getPresentZones).headOption
  }

  def anyContour : Chooser[String] = {
    case sd: CompoundSpiderDiagramOccurrence => None
    case sd: PrimarySpiderDiagramOccurrence =>
      sd.getAllContours.headOption
  }
}
