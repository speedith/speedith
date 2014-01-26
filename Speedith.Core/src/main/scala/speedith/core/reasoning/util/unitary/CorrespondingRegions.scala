package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zone, Region, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.Zones.allZonesForContours
import scala.collection.mutable

case class CorrespondingRegions(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val allPossibleZonesInDestination = allZonesForContours(destinationDiagram.getAllContours.toIterable.toSeq: _*)

  def areRegionsCorresponding(regionInSourceDiagram: Region, regionInDestinationDiagram: Region): Boolean = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)
    assertContoursOfRegionMatchContoursInDiagram(regionInDestinationDiagram, destinationDiagram)
    true
  }

  def correspondingRegion(regionInSourceDiagram: Region): Region = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)

    val rawCorrespondingRegion = if (destinationDiagram.getAllContours.subsetOf(sourceDiagram.getAllContours)) {
      getRegionWhenDestinationContoursAreSubset(regionInSourceDiagram)
    } else if (sourceDiagram.getAllContours.subsetOf(destinationDiagram.getAllContours)) {
      getRegionWhenSourceContoursAreSubset(regionInSourceDiagram)
    } else {
      throw new UnsupportedOperationException("Cannot calculate corresponding regions for diagrams that have distinct contours.")
    }
    new Region(withoutEmptyZones(rawCorrespondingRegion))
  }


  private def getRegionWhenSourceContoursAreSubset(regionInSourceDiagram: Region): mutable.Buffer[Zone] = {
    allPossibleZonesInDestination.filter {
      destinationZone =>
        regionInSourceDiagram.zones.exists {
          sourceZone =>
            sourceZone.getInContours.subsetOf(destinationZone.getInContours) &&
              sourceZone.getOutContours.subsetOf(destinationZone.getOutContours)
        }
    }
  }


  private def withoutEmptyZones(rawCorrespondingRegion: mutable.Buffer[Zone]): mutable.Buffer[Zone] = {
    rawCorrespondingRegion.filterNot {
      destinationZone =>
        destinationDiagram.getShadedZones.contains(destinationZone) &&
          !destinationDiagram.getHabitats.exists {
            case (spider, habitat) => habitat.zones.contains(destinationZone)
          }
    }
  }

  private def getRegionWhenDestinationContoursAreSubset(regionInSourceDiagram: Region): mutable.Buffer[Zone] = {
    allPossibleZonesInDestination.filter {
      destinationZone =>
        regionInSourceDiagram.zones.exists {
          sourceZone =>
            destinationZone.getInContours.subsetOf(sourceZone.getInContours) &&
              destinationZone.getOutContours.subsetOf(sourceZone.getOutContours)
        }
    }
  }

  private def assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram: Region, diagram: PrimarySpiderDiagram) {
    if (!regionInSourceDiagram.zones.forall(zone => zone.getAllContours == diagram.getAllContours)) {
      throw new IllegalArgumentException("The contours of the given region do not match the contours in the source diagram.")
    }
  }
}
