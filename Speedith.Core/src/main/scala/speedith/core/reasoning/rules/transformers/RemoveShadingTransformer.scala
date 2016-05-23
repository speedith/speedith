package speedith.core.reasoning.rules.transformers


import speedith.core.i18n.Translations._
import speedith.core.lang._
import speedith.core.reasoning.rules.SimpleInferenceRule
import speedith.core.reasoning.{ApplyStyle, RuleApplicationException}
import speedith.core.reasoning.args.{SubDiagramIndexArg, ZoneArg}

import scala.collection.JavaConversions._


/**
  * Transforms the [[PrimarySpiderDiagram]] referenced by the given [[ZoneArg]] by
  * removing the zone saved in this [[ZoneArg]] from the set of shaded zones.
  *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
class RemoveShadingTransformer (target : SubDiagramIndexArg, zones :  java.util.List[ZoneArg], applyStyle: ApplyStyle) extends IdTransformer{
  val subDiagramIndex = target.getSubDiagramIndex

  override def transform(psd: PrimarySpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == subDiagramIndex) {
      if (!SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
        if (applyStyle == ApplyStyle.GoalBased) {
          throw new TransformationException(i18n("RULE_NOT_NEGATIVE_POSITION"))
        } else {
          throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"))
        }
      }
      if ((zones.map(zarg => zarg.getZone) -- (psd.getShadedZones & psd.getPresentZones)).nonEmpty) {
        throw new RuleApplicationException("One of the selected zones is not shaded.")
      }
      SpiderDiagrams.createPrimarySD(psd.getHabitats, psd.getShadedZones -- zones.map(zarg => zarg.getZone), psd.getPresentZones)
//      EulerDiagrams.createPrimaryEulerDiagram(psd.getShadedZones -- zones.map(zarg => zarg.getZone), psd.getPresentZones)
    }
    else {
      null
    }
  }

}
