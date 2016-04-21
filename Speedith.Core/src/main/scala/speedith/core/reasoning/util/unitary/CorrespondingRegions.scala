package speedith.core.reasoning.util.unitary

import speedith.core.lang.Zones.allZonesForContours
import speedith.core.lang.{PrimarySpiderDiagram, Region, Zone}
import speedith.core.reasoning.rules.util.ReasoningUtils

import scala.collection.JavaConversions._
import scala.collection.mutable

case class CorrespondingRegions(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val allPossibleZonesInDestination = allZonesForContours(destinationDiagram.getAllContours.toIterable.toSeq: _*)

  def areRegionsCorresponding(regionInSourceDiagram: Region, regionInDestinationDiagram: Region): Boolean = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)
    assertContoursOfRegionMatchContoursInDiagram(regionInDestinationDiagram, destinationDiagram)
    true
  }

  def correspondingRegion(regionInSourceDiagram: Region): Region = {
    assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram, sourceDiagram)

    val rawCorrespondingRegion = if (destinationDiagram.getAllContours.subsetOf(sourceDiagram.getAllContours)) {
      getRegionWhenDestinationContoursAreSubset(regionInSourceDiagram)
    } else if (sourceDiagram.getAllContours.subsetOf(destinationDiagram.getAllContours)) {
      getRegionWhenSourceContoursAreSubset(regionInSourceDiagram)
    } else {
      getRegionGeneral(regionInSourceDiagram)
//      throw new UnsupportedOperationException("Cannot calculate corresponding regions for diagrams that have distinct contours.")
    }
    new Region(withoutEmptyZones(rawCorrespondingRegion))
  }


  private def getRegionWhenSourceContoursAreSubset(regionInSourceDiagram: Region): mutable.Buffer[Zone] = {
    val contoursOnlyInDestination = destinationDiagram.getAllContours -- sourceDiagram.getAllContours
    allPossibleZonesInDestination.filter {
      destinationZone =>
        ReasoningUtils.expand(destinationZone, contoursOnlyInDestination).forall(ex =>
          (regionInSourceDiagram.zones ++ (destinationDiagram.getShadedZones diff destinationDiagram.getPresentZones)).exists {
          sourceZone =>
            sourceZone.getInContours.subsetOf(ex.getInContours) &&
              sourceZone.getOutContours.subsetOf(ex.getOutContours)
        }
        )
    }
  }


  private def withoutEmptyZones(rawCorrespondingRegion: mutable.Buffer[Zone]): mutable.Buffer[Zone] = {
    rawCorrespondingRegion.filterNot {
      destinationZone =>
        (destinationDiagram.getShadedZones -- destinationDiagram.getPresentZones ).contains(destinationZone) &&
          !destinationDiagram.getHabitats.exists {
            case (spider, habitat) => habitat.zones.contains(destinationZone)
          }
    }
  }

  private def getRegionWhenDestinationContoursAreSubset(regionInSourceDiagram: Region): mutable.Buffer[Zone] = {
    val contoursOnlyInSource = sourceDiagram.getAllContours -- destinationDiagram.getAllContours
    allPossibleZonesInDestination.filter {
      destinationZone =>
        ReasoningUtils.expand(destinationZone, contoursOnlyInSource).forall( ex=>
          (regionInSourceDiagram.zones ++ (sourceDiagram.getShadedZones diff sourceDiagram.getPresentZones)).exists {
            sourceZone =>
              ex.getInContours.subsetOf(sourceZone.getInContours) &&
                ex.getOutContours.subsetOf(sourceZone.getOutContours)
          })

    }
  }

  private def getRegionGeneral(regionInSourceDiagram: Region) : mutable.Buffer[Zone] = {
    val contoursOnlyInSource = sourceDiagram.getAllContours -- destinationDiagram.getAllContours
    val contoursOnlyInTarget = destinationDiagram.getAllContours -- sourceDiagram.getAllContours
    val sourceExpansion = ReasoningUtils.expand(regionInSourceDiagram.zones, contoursOnlyInTarget)
    val sourceMissing = ReasoningUtils.expand((sourceDiagram.getShadedZones -- sourceDiagram.getPresentZones).toSet, contoursOnlyInTarget)
    val targetMissing = ReasoningUtils.expand((destinationDiagram.getShadedZones -- destinationDiagram.getShadedZones).toSet, contoursOnlyInSource)
    allPossibleZonesInDestination.filter( {
      destinationZone =>
        ReasoningUtils.expand(destinationZone, contoursOnlyInSource).forall( ex =>
          (sourceExpansion ++ sourceMissing ++ targetMissing).exists {
            sourceZone =>
              ex.equals(sourceZone)
          }
        )
    })
  }

  private def assertContoursOfRegionMatchContoursInDiagram(regionInSourceDiagram: Region, diagram: PrimarySpiderDiagram) {
    if (!regionInSourceDiagram.zones.forall(zone => zone.getAllContours == diagram.getAllContours)) {
      throw new IllegalArgumentException("The contours of the given region do not match the contours in the source diagram.")
    }
  }
}
