package speedith.core.lang.util

import speedith.core.lang.PrimarySpiderDiagram

import scala.collection.JavaConversions._

object ShadingUtils {

  def allShadedZonesHaveSameSpidersAsShadedZonesInOther(diagram: PrimarySpiderDiagram, otherDiagram: PrimarySpiderDiagram): Boolean = {
    val commonShadedZones = diagram.getShadedZones.intersect(otherDiagram.getShadedZones)
    commonShadedZones.forall(zone => diagram.getSpiderCountInZone(zone) == otherDiagram.getSpiderCountInZone(zone))
  }

  def anyShadedZoneHasFewerSpidersThanNonShadedZoneInOther(diagram: PrimarySpiderDiagram, otherDiagram: PrimarySpiderDiagram): Boolean = {
    diagram.getShadedZones.exists{
      zone =>
        !otherDiagram.getShadedZones.contains(zone) &&
          diagram.getSpiderCountInZone(zone) < otherDiagram.getSpiderCountInZone(zone)
    }
  }
}
