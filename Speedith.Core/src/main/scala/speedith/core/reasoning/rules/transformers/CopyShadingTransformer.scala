package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.args.ZoneArg
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction._
import speedith.core.reasoning.util.unitary.ShadingTransfer
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction

case class CopyShadingTransformer(compoundDiagramIndex: Int,
                                  zoneArg: ZoneArg)
  extends HeterogeneousTransformer(compoundDiagramIndex) {

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
    assertOperandsAreUnitary(currentDiagram)

    val diagramWithSpider = getSourceOperand(currentDiagram, compoundDiagramIndex, zoneArg)
    val diagramWithoutSpider = getTargetOperand(currentDiagram, compoundDiagramIndex, zoneArg)

    copyShading(diagramWithSpider, diagramWithoutSpider)
  }

  def copyShading(sourceDiagram: PrimarySpiderDiagram, targetDiagram: PrimarySpiderDiagram): SpiderDiagram = {
    try {
      val transformedDiagram = new ShadingTransfer(sourceDiagram, targetDiagram).transferShading(zoneArg.getZone)
      InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, sourceDiagram, transformedDiagram, zoneArg, compoundDiagramIndex)
    }
    catch {
      case e: Exception => {
        throw new TransformationException("Could not copy the spider. " + e.getMessage, e)
      }
    }
  }
}
