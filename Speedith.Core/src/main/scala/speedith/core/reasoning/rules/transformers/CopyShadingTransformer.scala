package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.args.ZoneArg
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction._
import speedith.core.reasoning.util.unitary.ShadingTransfer

import scala.collection.JavaConversions._

case class CopyShadingTransformer(compoundDiagramIndex: Int,
                                  zoneArgsPlain: java.util.Collection[ZoneArg])
  extends CompoundDiagramTransformer(compoundDiagramIndex) {

  var zoneArgs = zoneArgsPlain.toList

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
    assertOperandsAreUnitary(currentDiagram)

    val diagramWithSpider = getSourceOperand(currentDiagram, compoundDiagramIndex, zoneArgs.head)
    val diagramWithoutSpider = getTargetOperand(currentDiagram, compoundDiagramIndex, zoneArgs.head)

    copyShading(diagramWithSpider, diagramWithoutSpider)
  }

  def copyShading(sourceDiagram: PrimarySpiderDiagram, targetDiagram: PrimarySpiderDiagram): SpiderDiagram = {
    try {
      val transformedDiagram = new ShadingTransfer(sourceDiagram, targetDiagram).transferShading(zoneArgs.map(_.getZone))
      InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, sourceDiagram, transformedDiagram, zoneArgs.head, compoundDiagramIndex)
    }
    catch {
      case e: Exception => throw new TransformationException("Could not copy the shading. " + e.getMessage, e)
    }
  }
}
