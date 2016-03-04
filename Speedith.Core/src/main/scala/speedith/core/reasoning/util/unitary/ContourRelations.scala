package speedith.core.reasoning.util.unitary

import speedith.core.lang.{PrimarySpiderDiagram, Zone, Zones}

import scala.collection.JavaConversions._

class ContourRelations(diagram: PrimarySpiderDiagram) {

  def areContoursDisjoint(contourA: String, contourB: String): Boolean = {
    assertContoursPresentInDiagram(contourA, contourB)
    allSharedContoursAreShaded(contourA, contourB) && noSharedContoursHaveSpiders(contourA, contourB)
  }

  def contourContainsAnother(containerContour: String, otherContour: String): Boolean = {
    assertContoursPresentInDiagram(containerContour, otherContour)
    allZonesOfAOutsideBAreShaded(otherContour, containerContour) &&
      !spiderExistsInAButOutsideB(otherContour, containerContour)

  }

  private def allZonesOfAOutsideBAreShaded(contourA: String, contourB: String): Boolean = {
    val numberOfShadedZonesOutsideContainer = diagram.getShadedZones.count(shadedZone =>
      isZoneInAButNotB(shadedZone, contourA, contourB)
    )
    val numberOfAllPossibleShadedZonesOutsideContainer = 1 << (diagram.getAllContours.size() - 2)
    numberOfShadedZonesOutsideContainer == numberOfAllPossibleShadedZonesOutsideContainer
  }

  private def spiderExistsInAButOutsideB(contourA: String, contourB: String): Boolean = {
    diagram.getHabitats.values().flatMap(_.zones).exists(habitatZone =>
      isZoneInAButNotB(habitatZone, contourA, contourB)
    )
  }

  private def isZoneInAButNotB(shadedZone: Zone, contourA: String, contourB: String): Boolean = {
    Zones.isZonePartOfAllContours(shadedZone, contourA) && Zones.isZoneOutsideContours(shadedZone, contourB)
  }

  private def noSharedContoursHaveSpiders(contourA: String, contourB: String): Boolean = {
    val allZonesWithSpiders = diagram.getHabitats.values().flatMap(_.zones)
    allZonesWithSpiders.forall(zoneWithSpider => !Zones.isZonePartOfAllContours(zoneWithSpider, contourA, contourB))
  }

  private def assertContoursPresentInDiagram(contourA: String, contourB: String) {
    val allContours = diagram.getAllContours
    if (!allContours.contains(contourA) || !allContours.contains(contourB)) {
      throw new IllegalArgumentException("Both contours '" + contourA + "' and '$contourB' must be present in the diagram.")
    }
  }

  private def allSharedContoursAreShaded(contourA: String, contourB: String): Boolean = {
    val sharedShadedZones = Zones.getZonesInsideAllContours(diagram.getShadedZones, contourA, contourB)
    sharedShadedZones.size() == numberOfAllSharedZones(2)
  }

  private def numberOfAllSharedZones(numberOfTargetContours: Int): Int = {
    val numberOfAllContours = diagram.getAllContours.size()
    val numberOfRemainingContours = numberOfAllContours - numberOfTargetContours
    1 << numberOfRemainingContours
  }
}
