package speedith.core.reasoning.rules.transformers

import speedith.core.lang._

import speedith.core.reasoning.args.{ContourArg, SubDiagramIndexArg}
import speedith.core.reasoning.rules.util.ReasoningUtils

import scala.collection.JavaConversions._
import scala.collection.SortedMap

/** @author Sven Linker [s.linker@brighton.ac.uk]
  *
  *         Only works for Euler Diagrams!
 * Created by sl542 on 10/11/15.
 */
case class IntroduceContoursTransformer(target : SubDiagramIndexArg, contours : java.util.List[ContourArg]) extends IdTransformer {
  val subDiagramIndex = target.getSubDiagramIndex
  val contoursToAdd = contours.map(_.getContour).toSet

  private def regionWithNewContours(region: Iterable[Zone]): Set[Zone] = {
    region.map(zone => new Zone(zone.getInContours ++ contoursToAdd, zone.getOutContours )).toSet ++ region.map(zone => new Zone(zone.getInContours , zone.getOutContours ++ contoursToAdd )).toSet
  }

  def createHabitats(habitats: Map[String, Region], contoursToAdd: Set[String]): Map[String, Region] = {
    habitats map (s  => (s._1,Region(ReasoningUtils.regionWithNewContours(s._2.zones, contoursToAdd))))
  }

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (subDiagramIndex == diagramIndex) {
        if ((contoursToAdd & psd.getAllContours).nonEmpty ) {
          throw new TransformationException("The contours to be introduced must not be contained in the target diagram.")
        }
        SpiderDiagrams.createPrimarySD(createHabitats(psd.getHabitats.toMap, contoursToAdd), ReasoningUtils.shadedRegionWithNewContours(psd.getShadedZones.toSet,contoursToAdd),
          ReasoningUtils.regionWithNewContours(psd.getPresentZones,contoursToAdd) )

      /*        EulerDiagrams.createPrimaryEulerDiagram(
          ReasoningUtils.shadedRegionWithNewContours(psd.getShadedZones.toSet,contoursToAdd),
          ReasoningUtils.regionWithNewContours(psd.getPresentZones,contoursToAdd)
        ) */

    } else {
      null
    }
  }


}
