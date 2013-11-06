package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zone, PrimarySpiderDiagram}
import scala.collection.JavaConversions._

case class ZoneDestinations(sourceDiagram: PrimarySpiderDiagram,
                            referenceContour: String,
                            outZones: java.util.Set[Zone],
                            inZones: java.util.Set[Zone],
                            splitZones: java.util.Set[Zone])

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val contoursOnlyInSource: java.util.Set[String] = {
    sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  }

  def zonesInDestinationOutsideContour(sourceContour: String): java.util.Set[Zone] = {
    if (!contoursOnlyInSource.contains(sourceContour)) {
      throw new IllegalArgumentException("The contour '" + sourceContour + "' must be present only in the source diagram.")
    }

    val zonesInDestinationDiagram = destinationDiagram.getPresentZones ++ destinationDiagram.getHabitats.values().flatMap(_.getZones)
    val sourceContourRelations = new ContourRelations(sourceDiagram)
    val allContoursInSource = sourceDiagram.getAllContours

    zonesInDestinationDiagram.filter(destinationZone =>
      allContoursInSource.exists(commonContour =>
        destinationZone.getInContours.contains(commonContour) && sourceContourRelations.areContoursDisjoint(sourceContour, commonContour) ||
          destinationZone.getOutContours.contains(commonContour) && sourceContourRelations.contourContainsAnother(sourceContour, commonContour)
      ))
  }

}
