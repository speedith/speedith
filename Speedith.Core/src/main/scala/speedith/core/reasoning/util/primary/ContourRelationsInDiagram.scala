package speedith.core.reasoning.util.primary

import speedith.core.lang.{Zone, Zones, PrimarySpiderDiagram}
import scala.collection.JavaConversions._

class ContourRelationsInDiagram(diagram: PrimarySpiderDiagram) {

  def areContoursDisjoint(contourA: String, contourB: String): Boolean = {
    assertContoursPresentInDiagram(contourA, contourB)
    if (diagram.getShadedZonesCount == 0) {
      false
    } else {
      allSharedContoursAreShaded(contourA, contourB) && noSharedContoursHaveSpiders(contourA, contourB)
    }
  }

  def contourContainsAnother(containerContour: String, otherContour: String): Boolean = {
    assertContoursPresentInDiagram(containerContour, otherContour)
    val spiderInOtherContourExists = diagram.getHabitats.values().flatMap(_.getZones).exists(habitatZone =>
      isZoneInAButNotB(habitatZone, otherContour, containerContour)
    )
    if (spiderInOtherContourExists) {
      false
    } else {
      val numberOfShadedZonesOutsideContainer = diagram.getShadedZones.count(shadedZone =>
        isZoneInAButNotB(shadedZone, otherContour, containerContour)
      )
      val numberOfAllPossibleShadedZonesOutsideContainer = 1 << (diagram.getAllContours.size() - 2)
      numberOfShadedZonesOutsideContainer == numberOfAllPossibleShadedZonesOutsideContainer
    }
  }


  private def isZoneInAButNotB(shadedZone: Zone, contourA: String, contourB: String): Boolean = {
    Zones.isZonePartOfAllContours(shadedZone, contourA) && Zones.isZoneOutsideContours(shadedZone, contourB)
  }

  private def noSharedContoursHaveSpiders(contourA: String, contourB: String): Boolean = {
    val habitats = if (diagram.getHabitatsCount == 0) Nil else diagram.getHabitats.values().toIterable
    val allZonesWithSpiders = habitats.flatMap(_.getZones).toIterable
    allZonesWithSpiders.forall(zoneWithSpider => !Zones.isZonePartOfAllContours(zoneWithSpider, contourA, contourB))
  }

  private def assertContoursPresentInDiagram(contourA: String, contourB: String) {
    val allContours = diagram.getAllContours
    if (!allContours.contains(contourA) || !allContours.contains(contourB)) {
      throw new IllegalArgumentException(s"Both contours '$contourA' and '$contourB' must be present in the diagram.")
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
