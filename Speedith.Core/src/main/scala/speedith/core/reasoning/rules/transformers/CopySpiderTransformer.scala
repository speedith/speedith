package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction._
import scala.collection.JavaConversions._
import speedith.core.reasoning.args.SpiderArg
import speedith.core.reasoning.util.unitary.{SpiderTransfer, ZoneTransfer}
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction

case class CopySpiderTransformer(indexOfCompoundDiagram: Int, spiderArg: SpiderArg) extends IdTransformer {

  if (indexOfCompoundDiagram < 0) {
    throw new TransformationException("The target sub-diagram is not in a conjunction.")
  }

  def copySpider(sourceDiagram: PrimarySpiderDiagram, targetDiagram: PrimarySpiderDiagram): SpiderDiagram = {
    try {
      val transformedDiagram = new SpiderTransfer(sourceDiagram, targetDiagram).transferSpider(spiderArg.getSpider)
      InferenceTargetExtraction.createBinaryDiagram(Operator.Conjunction, sourceDiagram, transformedDiagram, spiderArg, indexOfCompoundDiagram)
    }
    catch {
      case e: Exception => {
        throw new TransformationException("Could not copy the spider. " + e.getMessage, e)
      }
    }
  }

  override def transform(currentDiagram: CompoundSpiderDiagram,
                         diagramIndex: Int,
                         parents: java.util.ArrayList[CompoundSpiderDiagram],
                         childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == indexOfCompoundDiagram) {
      assertIsConjunction(currentDiagram)
      assertOperandsAreUnitary(currentDiagram)

      val diagramWithSpider = getSourceOperand(currentDiagram, diagramIndex, spiderArg)
      val diagramWithoutSpider = getTargetOperand(currentDiagram, diagramIndex, spiderArg)

      assertSpiderIsInTargetDiagram(diagramWithSpider)
      copySpider(diagramWithSpider, diagramWithoutSpider)
    } else {
      null
    }
  }


  private def assertSpiderIsInTargetDiagram(diagramWithSpider: PrimarySpiderDiagram) {
    if (!diagramWithSpider.getSpiders.contains(spiderArg.getSpider)) {
      throw new TransformationException("The target unitary diagram does not contain the spider '" + spiderArg.getSpider + "', which was to be copied.")
    }
  }

  override def transform(psd: PrimarySpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertDiagramIsNotTarget(diagramIndex)
    null
  }


  override def transform(nsd: NullSpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertDiagramIsNotTarget(diagramIndex)
    null
  }

  private def assertDiagramIsNotTarget(diagramIndex: Int) {
    if (diagramIndex == indexOfCompoundDiagram) {
      throw new IllegalArgumentException("Could not apply this rule on the target diagram. The target diagram must be within a compound diagram.")
    }
  }
}
