package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.RuleApplicationException
import speedith.core.reasoning.args.{SubDiagramIndexArg, ZoneArg}

import scala.collection.JavaConversions._

/**
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
class IntroShadedZoneTransformer (target:  SubDiagramIndexArg, zones : java.util.List[ZoneArg]) extends IdTransformer {
  val subDiagramIndex = target.getSubDiagramIndex

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == subDiagramIndex) {
        if ( (zones.map(_.getZone) -- (psd.getShadedZones -- psd.getPresentZones)).nonEmpty) {
          throw new TransformationException("One of the selected zones is not missing.")
        }
        SpiderDiagrams.createPrimarySD(psd.getHabitats,psd.getShadedZones, psd.getPresentZones ++  zones.map(_.getZone))
    } else {
      null
    }
  }
}
