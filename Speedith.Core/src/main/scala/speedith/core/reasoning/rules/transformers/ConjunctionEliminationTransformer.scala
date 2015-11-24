package speedith.core.reasoning.rules.transformers

import speedith.core.reasoning.args.SubDiagramIndexArg
import speedith.core.lang.{SpiderDiagram, CompoundSpiderDiagram}
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction

case class ConjunctionEliminationTransformer(compundDiagramIndex : Int, childDiagramIndexArg : SubDiagramIndexArg)
  extends CompoundDiagramTransformer(compundDiagramIndex) {

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)
     if(InferenceTargetExtraction.isLeftOperand(childDiagramIndexArg, compundDiagramIndex)) {
       currentDiagram.getOperand(0)
     } else {
       currentDiagram.getOperand(1)
     }


  }
}
