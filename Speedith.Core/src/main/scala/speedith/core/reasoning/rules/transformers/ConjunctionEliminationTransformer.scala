package speedith.core.reasoning.rules.transformers

import speedith.core.reasoning.args.SubDiagramIndexArg
import speedith.core.lang.{SpiderDiagram, CompoundSpiderDiagram}
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._

case class ConjunctionEliminationTransformer(subDiagramIndexArg: SubDiagramIndexArg)
  extends CompoundDiagramTransformer(subDiagramIndexArg.getSubDiagramIndex) {

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
    currentDiagram.getOperand(0)
  }
}
