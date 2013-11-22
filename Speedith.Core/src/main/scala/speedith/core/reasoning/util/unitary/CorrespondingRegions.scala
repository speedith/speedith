package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Region, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.Zones.allZonesForContours

class CorrespondingRegions(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val allPossibleZonesInDestination = allZonesForContours(destinationDiagram.getAllContours.toIterable.toSeq: _*)

  def areRegionsCorresponding(regionInSourceDiagram: Region, regionInDestinationDiagram: Region): Boolean = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)
    assertContoursOfRegionMatchContoursInDiagram(regionInDestinationDiagram, destinationDiagram)
    true
  }

  def correspondingRegion(regionInSourceDiagram: Region): Region = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)

    new Region(allPossibleZonesInDestination.filter(destinationZone =>
      regionInSourceDiagram.getZones.exists(sourceZone =>
        destinationZone.getInContours.subsetOf(sourceZone.getInContours) &&
          destinationZone.getOutContours.subsetOf(sourceZone.getOutContours)
      )
    ))
  }

  private def assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram: Region, diagram: PrimarySpiderDiagram) {
    if (!regionInSourceDiagram.getZones.forall(zone => zone.getAllContours == diagram.getAllContours)) {
      throw new IllegalArgumentException("The contours of the given region do not match the contours in the source diagram.")
    }
  }
}
