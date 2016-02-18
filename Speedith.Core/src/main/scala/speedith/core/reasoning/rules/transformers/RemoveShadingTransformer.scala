package speedith.core.reasoning.rules.transformers


import speedith.core.lang._
import speedith.core.reasoning.RuleApplicationException
import speedith.core.reasoning.args.ZoneArg

import scala.collection.JavaConversions._


/**
  * Transforms the [[PrimarySpiderDiagram]] referenced by the given [[ZoneArg]] by
  * removing the zone saved in this [[ZoneArg]] from the set of shaded zones.
  *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
class RemoveShadingTransformer (target:  ZoneArg) extends IdTransformer{
  val subDiagramIndex = target.getSubDiagramIndex

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == subDiagramIndex) {
        if (!(psd.getShadedZones & psd.getPresentZones).contains(target.getZone) ) {
          throw new RuleApplicationException("Selected zone is not shaded.")
        }
        EulerDiagrams.createPrimaryEulerDiagram(psd.getShadedZones - target.getZone, psd.getPresentZones)
    }
    else {
      null
    }
  }

}
