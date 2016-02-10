package speedith.core.reasoning.rules.transformers



import speedith.core.lang._
import speedith.core.reasoning.RuleApplicationException
import speedith.core.reasoning.args.ZoneArg

import scala.collection.JavaConversions._

/**
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
class RemoveShadedZoneTransformer (target:  ZoneArg) extends IdTransformer{
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
        if (target.getZone.getInContoursCount ==0) {
          throw new RuleApplicationException("Cannot remove the outer zone")
        }
        EulerDiagrams.createPrimaryEulerDiagram(psd.getShadedZones , psd.getPresentZones- target.getZone)
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
