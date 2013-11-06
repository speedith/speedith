package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zone, PrimarySpiderDiagram}
import scala.collection.JavaConversions._

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val contoursOnlyInSource: java.util.Set[String] = {
    sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  }

  private val sourceContourRelations = new ContourRelations(sourceDiagram)
  private val contoursInBothDiagrams: Set[String] = sourceDiagram.getAllContours.toSet

  def zonesInDestinationOutsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allZonesInDestinationDiagram.filter(destinationZone =>
      contoursInBothDiagrams.exists(commonContour =>
        (destinationZone.getInContours.contains(commonContour) && sourceContourRelations.areContoursDisjoint(sourceContour, commonContour)) ||
          (destinationZone.getOutContours.contains(commonContour) && sourceContourRelations.contourContainsAnother(commonContour, sourceContour))
      ))
  }


  private val allZonesInDestinationDiagram: Set[Zone] = {
    (destinationDiagram.getPresentZones ++ destinationDiagram.getHabitats.values().flatMap(_.getZones)).toSet
  }

  def zonesInDestinationInsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allZonesInDestinationDiagram.filter(destinationZone =>
      contoursInBothDiagrams.exists(contour =>
        destinationZone.getInContours.contains(contour) && sourceContourRelations.contourContainsAnother(sourceContour, contour)
      )
    )
  }


  private def assertContourOnlyInSource(sourceContour: String) {
    if (!contoursOnlyInSource.contains(sourceContour)) {
      throw new IllegalArgumentException("The contour '" + sourceContour + "' must be present only in the source diagram.")
    }
  }
}
