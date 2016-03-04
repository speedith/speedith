package speedith.core.reasoning.rules.transformers

import speedith.core.lang._

import scala.collection.mutable

class DoubleNegationEliminationTransformer(targetSubDiagramIndex: Int) extends SimpleTransformer {

  protected def transform(spiderDiagram: SpiderDiagram, currentDiagramIndex: Int, parents: mutable.Buffer[CompoundSpiderDiagram], childIndices: mutable.Buffer[Int]): SpiderDiagram = {
    if (currentDiagramIndex == targetSubDiagramIndex) {
      spiderDiagram match {
        case csd: CompoundSpiderDiagram =>
          extractDoublyNegatedDiagram(csd)
        case _ => reportNotDoublyNegated
      }
    } else {
      null
    }
  }

  private def extractDoublyNegatedDiagram(diagram: CompoundSpiderDiagram): SpiderDiagram = {
    if (diagram.getOperator == Operator.Negation) {
      diagram.getOperand(0) match {
        case csd: CompoundSpiderDiagram =>
          if (csd.getOperator == Operator.Negation) {
            return csd.getOperand(0)
          }
        case _ =>
      }
    }
    reportNotDoublyNegated
  }

  private def reportNotDoublyNegated: Nothing = {
    throw new TransformationException("Double negation elimination may be applied only to doubly-negated diagrams.")
  }
}
