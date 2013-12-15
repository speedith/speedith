package speedith.core.reasoning.rules.transformers

import speedith.core.lang._

abstract class CompoundDiagramTransformer(compoundDiagramIndex: Int) extends IdTransformer {

  if (compoundDiagramIndex < 0) {
    throw new TransformationException("The target sub-diagram is not in a conjunction.")
  }

  def transform(csd: CompoundSpiderDiagram, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram

  override def transform(csd: CompoundSpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    if (diagramIndex == compoundDiagramIndex) {
      transform(csd, parents, childIndices)
    } else {
      null
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

  protected def assertDiagramIsNotTarget(diagramIndex: Int) {
    if (diagramIndex == compoundDiagramIndex) {
      throw new IllegalArgumentException("Could not apply this rule on the target diagram. The target diagram must be within a compound diagram.")
    }
  }
}
