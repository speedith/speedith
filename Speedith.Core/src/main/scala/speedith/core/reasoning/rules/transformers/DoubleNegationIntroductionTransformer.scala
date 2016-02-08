package speedith.core.reasoning.rules.transformers

import speedith.core.lang._

import scala.collection.mutable

class DoubleNegationIntroductionTransformer(targetSubDiagramIndex: Int) extends SimpleTransformer {

  override protected def transform(spiderDiagram: SpiderDiagram, currentDiagramIndex: Int, parents: mutable.Buffer[CompoundSpiderDiagram], childIndices: mutable.Buffer[Int]): SpiderDiagram = {
    if (currentDiagramIndex == targetSubDiagramIndex) {
      SpiderDiagrams.createCompoundSD(Operator.Negation, SpiderDiagrams.createCompoundSD(Operator.Negation, spiderDiagram))
    }
    else {
      null
    }
  }
}