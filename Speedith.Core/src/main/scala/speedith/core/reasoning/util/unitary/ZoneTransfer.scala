package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zones, Zone, PrimarySpiderDiagram}
import scala.collection.JavaConversions._

case class ZoneDestinations(sourceDiagram: PrimarySpiderDiagram,
                            referenceContour: String,
                            outZones: java.util.Set[Zone],
                            inZones: java.util.Set[Zone],
                            splitZones: java.util.Set[Zone])

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  def contoursOnlyInSource(): java.util.Set[String] = {
    sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  }

  def destinationZonesForSourceContour(sourceContour: String): ZoneDestinations = {
    if (!contoursOnlyInSource().contains(sourceContour)) {
      throw new IllegalArgumentException("The contour '" + sourceDiagram + "' is not present only in the source diagram.")
    }
    val allZonesInSource = sourceDiagram.getPresentZones ++ sourceDiagram.getHabitats.values().flatMap(_.getZones)

    ZoneDestinations(sourceDiagram, sourceContour, Set.empty[Zone], Set.empty[Zone], Set.empty[Zone])
  }

}
