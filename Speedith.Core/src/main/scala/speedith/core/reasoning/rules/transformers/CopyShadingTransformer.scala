package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.args.ZoneArg
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction._
import speedith.core.reasoning.util.unitary.ShadingTransfer
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction
import scala.collection.JavaConversions._

case class CopyShadingTransformer(compoundDiagramIndex: Int,
                                  zoneArgsPlain: java.util.Collection[ZoneArg])
  extends HeterogeneousTransformer(compoundDiagramIndex) {

  var zoneArgs = zoneArgsPlain.toList

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
    assertOperandsAreUnitary(currentDiagram)

    val diagramWithSpider = getSourceOperand(currentDiagram, compoundDiagramIndex, zoneArgs(0))
    val diagramWithoutSpider = getTargetOperand(currentDiagram, compoundDiagramIndex, zoneArgs(0))

    copyShading(diagramWithSpider, diagramWithoutSpider)
  }

  def copyShading(sourceDiagram: PrimarySpiderDiagram, targetDiagram: PrimarySpiderDiagram): SpiderDiagram = {
    try {
      val transformedDiagram = new ShadingTransfer(sourceDiagram, targetDiagram).transferShading(zoneArgs.map(_.getZone))
      InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, sourceDiagram, transformedDiagram, zoneArgs(0), compoundDiagramIndex)
    }
    catch {
      case e: Exception => {
        throw new TransformationException("Could not copy the spider. " + e.getMessage, e)
      }
    }
  }
}
