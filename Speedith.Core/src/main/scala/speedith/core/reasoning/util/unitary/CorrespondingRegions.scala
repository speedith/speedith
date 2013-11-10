package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Region, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.Zones.allZonesForContours

class CorrespondingRegions(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  def correspondingRegion(regionInSourceDiagram: Region): Region = {
    assertContoursOfRegionMatchSourceDiagram(regionInSourceDiagram)

    val allPossibleZonesInDestination = allZonesForContours(destinationDiagram.getAllContours.toIterable.toSeq: _*)

    new Region(allPossibleZonesInDestination.filter(destinationZone =>
      regionInSourceDiagram.getZones.exists(sourceZone =>
        destinationZone.getInContours.subsetOf(sourceZone.getInContours) &&
        destinationZone.getOutContours.subsetOf(sourceZone.getOutContours)
      )
    ))
  }

  private def assertContoursOfRegionMatchSourceDiagram(regionInSourceDiagram: Region) {
    if (!regionInSourceDiagram.getZones.forall(zone => zone.getAllContours == sourceDiagram.getAllContours)) {
      throw new IllegalArgumentException("The contours of the given region do not match the contours in the source diagram.")
    }
  }
}
