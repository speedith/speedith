package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.args.SpiderArg
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction._
import speedith.core.reasoning.util.unitary.SpiderTransfer

case class CopySpiderTransformer(compoundDiagramIndex: Int, spiderArg: SpiderArg) extends CompoundDiagramTransformer(compoundDiagramIndex) {

  override def transform(currentDiagram: CompoundSpiderDiagram,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
    assertOperandsAreUnitary(currentDiagram)

    val diagramWithSpider = getSourceOperand(currentDiagram, compoundDiagramIndex, spiderArg)
    val diagramWithoutSpider = getTargetOperand(currentDiagram, compoundDiagramIndex, spiderArg)

    assertSpiderIsInSourceDiagram(diagramWithSpider)
    copySpider(diagramWithSpider, diagramWithoutSpider)
  }

  private def copySpider(sourceDiagram: PrimarySpiderDiagram, targetDiagram: PrimarySpiderDiagram): SpiderDiagram = {
    try {
      val transformedDiagram = new SpiderTransfer(sourceDiagram, targetDiagram).transferSpider(spiderArg.getSpider)
      InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, sourceDiagram, transformedDiagram, spiderArg, compoundDiagramIndex)
    }
    catch {
      case e: Exception =>
        throw new TransformationException("Could not copy the spider. " + e.getMessage, e)
    }
  }


  private def assertSpiderIsInSourceDiagram(diagramWithSpider: PrimarySpiderDiagram) {
    if (!diagramWithSpider.getSpiders.contains(spiderArg.getSpider)) {
      throw new TransformationException("The target unitary diagram does not contain the spider '" + spiderArg.getSpider + "', which was to be copied.")
    }
  }
}
