package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zones, Region, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.Zones.allZonesForContours

class CorrespondingRegions(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {
  def correspondingRegion(region: Region): Region = {
    if (region.getZones.exists(zone => !(zone.getInContours ++ zone.getOutContours).subsetOf(sourceDiagram.getAllContours))) {
      throw new IllegalArgumentException("The region contains contours that are not present in the source diagram.")
    }
    val allPossibleZones = allZonesForContours(destinationDiagram.getAllContours.toIterable.toSeq:_*)
    val firstZoneInRegion = region.getZones.first()
    val commonContours = destinationDiagram.getAllContours.intersect(firstZoneInRegion.getAllContours)
    new Region(
      Zones.getZonesOutsideContours(
        Zones.getZonesInsideAllContours(
          allPossibleZones,
          firstZoneInRegion.getInContours.toIterable.toSeq:_*
        ),
        firstZoneInRegion.getOutContours.toIterable.toSeq:_*
      )
    )
  }
}
