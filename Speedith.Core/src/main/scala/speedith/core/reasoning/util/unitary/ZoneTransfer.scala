package speedith.core.reasoning.util.unitary

import speedith.core.lang.{Zones, Region, Zone, PrimarySpiderDiagram}
import scala.collection.JavaConversions._
import speedith.core.lang.SpiderDiagrams.createPrimarySD

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val contoursOnlyInSource: java.util.Set[String] = sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  private val sourceContourRelations = new ContourRelations(sourceDiagram)
  private val contoursInSourceDiagram: Set[String] = sourceDiagram.getAllContours.toSet
  private val allVisibleZonesInDestinationDiagram: Set[Zone] = (destinationDiagram.getPresentZones ++ destinationDiagram.getHabitats.values().flatMap(_.zones)).toSet
  private val allPossibleZonesInDestinationDiagram: Set[Zone] = Zones.allZonesForContours(destinationDiagram.getAllContours.toSeq:_*).toSet

  def transferContour(contourFromSource: String): PrimarySpiderDiagram = {
    assertContourOnlyInSource(contourFromSource)

    val zonesIn = zonesInDestinationInsideContour(contourFromSource)
    val zonesOut = zonesInDestinationOutsideContour(contourFromSource)
    val splitZones = allVisibleZonesInDestinationDiagram -- (zonesOut ++ zonesIn)

    val spiderHabitats = destinationDiagram.getHabitats.map {
      case (spider, habitat) => (spider, new Region(
        (zonesOut ++ splitZones).intersect(habitat.zones).map(addOutContourToZone(_, contourFromSource)) ++
        (zonesIn ++ splitZones).intersect(habitat.zones).map(addInContourToZone(_, contourFromSource))
      ))
    }

    val shadedZones = Zones.sameRegionWithNewContours(destinationDiagram.getShadedZones, contourFromSource) ++
      zonesOut.map(addInContourToZone(_, contourFromSource)) ++
      zonesIn.map(addOutContourToZone(_, contourFromSource))

    val presentZones = (zonesOut.intersect(allVisibleZonesInDestinationDiagram) ++ splitZones).map(zone => addOutContourToZone(zone, contourFromSource)) ++
      (zonesIn.intersect(allVisibleZonesInDestinationDiagram) ++ splitZones).map(zone => addInContourToZone(zone, contourFromSource))

    createPrimarySD(spiderHabitats.keySet, spiderHabitats, shadedZones, presentZones)
  }


  def zonesInDestinationOutsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allPossibleZonesInDestinationDiagram.filter(destinationZone =>
      contoursInSourceDiagram.exists(commonContour =>
        (destinationZone.getInContours.contains(commonContour) && sourceContourRelations.areContoursDisjoint(sourceContour, commonContour)) ||
          (destinationZone.getOutContours.contains(commonContour) && sourceContourRelations.contourContainsAnother(commonContour, sourceContour))
      ))
  }

  def zonesInDestinationInsideContour(sourceContour: String): java.util.Set[Zone] = {
    assertContourOnlyInSource(sourceContour)

    allPossibleZonesInDestinationDiagram.filter(destinationZone =>
      contoursInSourceDiagram.exists(contour =>
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

  private def assertContourOnlyInSource(sourceContour: String) {
    if (!contoursOnlyInSource.contains(sourceContour)) {
      throw new IllegalArgumentException("The contour '" + sourceContour + "' must be present only in the source diagram.")
    }
  }
}