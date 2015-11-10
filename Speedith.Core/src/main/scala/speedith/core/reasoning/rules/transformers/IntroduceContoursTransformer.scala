package speedith.core.reasoning.rules.transformers

import java.util

import speedith.core.lang._
import speedith.core.reasoning.RuleApplicationException
import speedith.core.reasoning.args.{ContourArg, SubDiagramIndexArg}
import scala.collection.JavaConversions._
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

/*  private def shadedRegionWithNewContours(region: Set[Zone]): Set[Zone] = {
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
*/
  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (subDiagramIndex == diagramIndex) {
      try {
        if ((contoursToAdd & psd.getAllContours).nonEmpty ) {
          throw new RuleApplicationException("The contours to be introduced must not be contained in the target diagram.")
        }
        EulerDiagrams.createPrimaryEulerDiagram(
          regionWithNewContours(psd.getShadedZones.toSet),
          regionWithNewContours(psd.getPresentZones)
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
