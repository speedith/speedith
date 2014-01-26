package speedith.core.reasoning.rules.transformers

import speedith.core.reasoning.args.ContourArg
import speedith.core.lang._
import scala.collection.JavaConversions._

case class RemoveContoursTransformer(contourArgs: java.util.List[ContourArg]) extends IdTransformer {

  val subDiagramIndex = contourArgs(0).getSubDiagramIndex
  val contoursToRemove = contourArgs.map(_.getContour).toSet

  private def regionWithoutContours(region: Iterable[Zone]): Set[Zone] = {
    region.map(zone => new Zone(zone.getInContours -- contoursToRemove, zone.getOutContours -- contoursToRemove)).toSet
  }

  private def shadedRegionWithoutContours(region: Set[Zone]): Set[Zone] = {
    var shadedRegion = region
    for (contourToRemove <- contoursToRemove) {
      shadedRegion = shadedRegion.filter(zone =>
        zone.getInContours.contains(contourToRemove) &&
          shadedRegion.contains(new Zone(zone.getInContours - contourToRemove, zone.getOutContours + contourToRemove))
      )
      shadedRegion = shadedRegion.map(zone => new Zone(zone.getInContours - contourToRemove, zone.getOutContours - contourToRemove)).toSet
    }
    shadedRegion
  }

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (subDiagramIndex == diagramIndex) {
      try {
        SpiderDiagrams.createPrimarySD(
          psd.getSpiders,
          psd.getHabitats.map {
            case (spider, habitat) => (spider, new Region(regionWithoutContours(habitat.zones)))
          },
          shadedRegionWithoutContours(psd.getShadedZones.toSet),
          regionWithoutContours(psd.getPresentZones)
        )
      }
      catch {
        case e: Throwable =>
          println(e)
          e.printStackTrace()
          throw e
      }
    } else {
      null
    }
  }
}
