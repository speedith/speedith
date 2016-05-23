package speedith.core.reasoning.util.unitary

import java.util

import speedith.core.lang._
import speedith.core.reasoning.rules.util.ReasoningUtils

import scala.collection.JavaConversions._



/** Implementation of the topological zone transfer used in the Readith project
  * for the CopyContour rule.
  * Only works for normalised Euler diagrams, i.e. SpiderDiagrams without Spiders, where
  * all visible zones are in the list of present zones!
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class ZoneTransferTopological(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  val contoursOnlyInSource: java.util.Set[String] = sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  val contoursOnlyInDestination: java.util.Set[String] = destinationDiagram.getAllContours.diff(sourceDiagram.getAllContours)
  private val sourceContourRelations = new ContourRelations(sourceDiagram)
  private val contoursInSourceDiagram: Set[String] = sourceDiagram.getAllContours.toSet
  private val allVisibleZonesInDestinationDiagram: Set[Zone] = destinationDiagram.getPresentZones.toSet
  private val allPossibleZonesInDestinationDiagram: Set[Zone] = Zones.allZonesForContours(destinationDiagram.getAllContours.toSeq:_*).toSet



  def transferContour (contourFromSource : String) : PrimarySpiderDiagram ={
   assertContourOnlyInSource(contourFromSource)
    // this implementation is horribly inefficient (several possibly exponential expandings)
    // but works straightforwardly like the written procedure

    // compute the expansions of the missing zones in source and target
    val sourceDiagramMZExpansion = ReasoningUtils.expand(sourceDiagram.getShadedZones.toSet -- sourceDiagram.getPresentZones, contoursOnlyInDestination )
    val destinationDiagramMZExpansion = ReasoningUtils.expand(destinationDiagram.getShadedZones.toSet -- destinationDiagram.getPresentZones, contoursOnlyInSource )
    // compute the expansion of the zones the contour to copy is a) contained in and b) not contained in
    val in = ReasoningUtils.expand(sourceDiagram.getPresentZones.filter(z => z.getInContours.contains(contourFromSource)).toSet, contoursOnlyInDestination)
    val out = ReasoningUtils.expand(sourceDiagram.getPresentZones.filter(z => z.getOutContours.contains(contourFromSource)).toSet, contoursOnlyInDestination)

    // add the missing zones of the source and target to prevent these sets from being computed several times
    val inMZ = in ++sourceDiagramMZExpansion++destinationDiagramMZExpansion
    val outMZ = out ++ sourceDiagramMZExpansion++destinationDiagramMZExpansion
    // all zones that are either shaded and visible or already corresponding to missing zones in the source
    // are free, i.e. they have to be ignored for the initial computation of Z_i, Z_o or Z_s
    val freeZones =  (destinationDiagram.getPresentZones & destinationDiagram.getShadedZones) ++
      destinationDiagram.getPresentZones.filter(z =>  ReasoningUtils.expand(new util.HashSet[Zone]().toSet + z, contoursOnlyInSource).subsetOf(sourceDiagramMZExpansion))
    // compute set of zones in Z_i (no free zones!)
    val inZones = destinationDiagram.getPresentZones.filter(z => !freeZones.contains(z) && ReasoningUtils.expand(new util.HashSet[Zone]().toSet + z, contoursOnlyInSource).subsetOf(inMZ))

    // compute set of zones in Z_o (no free zones!)
    val outZones = destinationDiagram.getPresentZones.filter(z => !freeZones.contains(z) && ReasoningUtils.expand(new util.HashSet[Zone]().toSet + z, contoursOnlyInSource).subsetOf(outMZ))
    // the rest of the non-free zones are definitely in Z_s
    val splitZones = allVisibleZonesInDestinationDiagram.diff(freeZones) -- (inZones ++ outZones)

    // we now have to compute, to which of the sets Z_i, Z_o or Z_s the free zones are added
    val freeOutZones = freeZones.filter(z => (ReasoningUtils.expand(new util.HashSet[Zone]().toSet+z, contoursOnlyInSource) -- sourceDiagramMZExpansion).forall(z2 => !z2.getInContours.contains(contourFromSource)))
    val freeInZones = freeZones.filter( { z =>
      val X = ReasoningUtils.expand(new util.HashSet[Zone]().toSet+z, contoursOnlyInSource) -- sourceDiagramMZExpansion
      X.nonEmpty && X.forall(z2 => z2.getInContours.contains(contourFromSource))
    })
    val freeSplitZones = freeZones -- (freeOutZones ++ freeInZones)

    // add the free zones to the according sets
    val zonesIn = inZones ++ freeInZones
    val zonesOut = outZones ++ freeOutZones
    val zonesSplit = splitZones ++ freeSplitZones

    val spiderHabitats = destinationDiagram.getHabitats.map {
      case (spider, habitat) => (spider, new Region(
        (zonesOut ++ zonesSplit).intersect(habitat.zones).map(addOutContourToZone(_, contourFromSource)) ++
          (zonesIn ++ zonesSplit).intersect(habitat.zones).map(addInContourToZone(_, contourFromSource))
      ))
    }

    val shadedZones = Zones.sameRegionWithNewContours(destinationDiagram.getShadedZones, contourFromSource) ++
      zonesOut.map(addInContourToZone(_, contourFromSource)) ++
      zonesIn.map(addOutContourToZone(_, contourFromSource))


    val presentZones = (zonesOut.intersect(allVisibleZonesInDestinationDiagram) ++ zonesSplit).map(zone => addOutContourToZone(zone, contourFromSource)) ++
      (zonesIn.intersect(allVisibleZonesInDestinationDiagram) ++ zonesSplit).map(zone => addInContourToZone(zone, contourFromSource))

    SpiderDiagrams.createPrimarySD(spiderHabitats, shadedZones, presentZones)
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
