package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zones, Region, Zone, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.SpiderDiagrams.createPrimarySD

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val contoursOnlyInSource: java.util.Set[String] = sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  private val sourceContourRelations = new ContourRelations(sourceDiagram)
  private val contoursInBothDiagrams: Set[String] = sourceDiagram.getAllContours.toSet

  def transferContour(contourFromSource: String): PrimarySpiderDiagram = {
    assertContourOnlyInSource(contourFromSource)

    val zonesIn = zonesInDestinationInsideContour(contourFromSource)
    val zonesOut = zonesInDestinationOutsideContour(contourFromSource)
    val splitZones = allZonesInDestinationDiagram -- (zonesOut ++ zonesIn)

    val spiderHabitats = destinationDiagram.getHabitats.map {
      case (spider, habitat) => (spider, new Region(
        (zonesOut ++ splitZones).intersect(habitat.getZones).map(addOutContourToZone(_, contourFromSource)) ++
        (zonesIn ++ splitZones).intersect(habitat.getZones).map(addInContourToZone(_, contourFromSource))
      ))
    }

    val shadedZones = Zones.sameRegionWithNewContours(destinationDiagram.getShadedZones, contourFromSource) ++
      zonesOut.map(addInContourToZone(_, contourFromSource)) ++
      zonesIn.map(addOutContourToZone(_, contourFromSource))

    val presentZones = (zonesOut ++ splitZones).map(zone => addOutContourToZone(zone, contourFromSource)) ++
      (zonesIn ++ splitZones).map(zone => addInContourToZone(zone, contourFromSource))

    createPrimarySD(spiderHabitats.keySet, spiderHabitats, shadedZones, presentZones)
  }


  def zonesInDestinationOutsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allZonesInDestinationDiagram.filter(destinationZone =>
      contoursInBothDiagrams.exists(commonContour =>
        (destinationZone.getInContours.contains(commonContour) && sourceContourRelations.areContoursDisjoint(sourceContour, commonContour)) ||
          (destinationZone.getOutContours.contains(commonContour) && sourceContourRelations.contourContainsAnother(commonContour, sourceContour))
      ))
  }

  def zonesInDestinationInsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allZonesInDestinationDiagram.filter(destinationZone =>
      contoursInBothDiagrams.exists(contour =>
        destinationZone.getInContours.contains(contour) && sourceContourRelations.contourContainsAnother(sourceContour, contour)
      )
    )
  }

  private def addInContourToZone(zone: Zone, contourFromSource: String): Zone = {
    zone.withInContours((zone.getInContours + contourFromSource).toSeq: _*)
  }

  private def addOutContourToZone(zone: Zone, contourFromSource: String): Zone = {
    zone.withOutContours((zone.getOutContours + contourFromSource).toSeq: _*)
  }

  private val allZonesInDestinationDiagram: Set[Zone] = {
    (destinationDiagram.getPresentZones ++ destinationDiagram.getHabitats.values().flatMap(_.getZones)).toSet
  }

  private def assertContourOnlyInSource(sourceContour: String) {
    if (!contoursOnlyInSource.contains(sourceContour)) {
      throw new IllegalArgumentException("The contour '" + sourceContour + "' must be present only in the source diagram.")
    }
  }
}
