package speedith.core.reasoning.rules.transformers

import speedith.core.lang.{SpiderDiagram, CompoundSpiderDiagram}
import speedith.core.reasoning.args.ZoneArg

case class CopyShadingTransformer(compoundDiagramIndex: Int,
                                  transformationTarget: ZoneArg)
  extends HeterogeneousTransformer(compoundDiagramIndex) {

  def transform(csd: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    null
  }
}
