package speedith.core.reasoning.rules.transformers

import java.util

import speedith.core.lang._
import speedith.core.reasoning.RuleApplicationException
import speedith.core.reasoning.args.{ZoneArg, SubDiagramIndexArg}
import scala.collection.JavaConversions._


/**
 * Created by sl542 on 11/11/15.
 */
class RemoveShadingTransformer (target:  ZoneArg) extends IdTransformer{
  val subDiagramIndex = target.getSubDiagramIndex

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == subDiagramIndex) {
      try{
        if (!(psd.getShadedZones & psd.getPresentZones).contains(target.getZone) ) {
          throw new RuleApplicationException("Selected zone is not shaded.")
        }
        EulerDiagrams.createPrimaryEulerDiagram(psd.getShadedZones - target.getZone, psd.getPresentZones)
      }
      catch {
        case e: Throwable =>
        println(e)
        e.printStackTrace()
        throw e
      }
    }
    else {
      null;
    }
  }

}