package speedith.core.reasoning.util.unitary

import java.util

import speedith.core.lang.{PrimarySpiderDiagram, Region, TransformationException, Zone}

import scala.collection.JavaConversions._

case class ShadingTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {



  def transferShading(shadedZones: Zone*): PrimarySpiderDiagram = {
    assertZonesInSourceShaded(shadedZones)

    val correspondingRegion = CorrespondingRegions(sourceDiagram, destinationDiagram).correspondingRegion(new Region(shadedZones))
    assertNonEmptyRegion(correspondingRegion)

    destinationDiagram.addShading(correspondingRegion.zones)
  }

  def transferShading(shadedZones: util.Collection[Zone]): PrimarySpiderDiagram = {
    transferShading(shadedZones.toSeq:_*)
  }

  private def assertZonesInSourceShaded(zones: Seq[Zone]): Unit = {
    val nonShadedZone = zones.find(!sourceDiagram.getShadedZones.contains(_))
    if (nonShadedZone.isDefined) {
      throw new TransformationException("The zone '" + nonShadedZone.get + "' is not shaded in the source unitary diagram.")
    }
  }

  private def assertNonEmptyRegion(correspondingRegion: Region): Unit = {
    if (correspondingRegion.zones.isEmpty){
      throw new TransformationException("Selected region does not correspond to a region in target diagram")
    }
  }

}
