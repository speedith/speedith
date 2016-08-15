package speedith.core.reasoning.rules.transformers

import speedith.core.lang.{TransformationException, CompoundSpiderDiagram, SpiderDiagram}
import speedith.core.reasoning.ApplyStyle
import speedith.core.reasoning.args.SubDiagramIndexArg
import speedith.core.reasoning.rules.SimpleInferenceRule
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._
import speedith.core.reasoning.rules.transformers.util.InferenceTargetExtraction
import speedith.core.i18n.Translations._

case class ConjunctionEliminationTransformer(compundDiagramIndex : Int, childDiagramIndexArg : SubDiagramIndexArg, applyStyle: ApplyStyle)
  extends CompoundDiagramTransformer(compundDiagramIndex) {

  def transform(currentDiagram: CompoundSpiderDiagram,
                parents: java.util.ArrayList[CompoundSpiderDiagram],
                childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    assertIsConjunction(currentDiagram)


    if (!SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
      if (applyStyle == ApplyStyle.GoalBased) {
        throw new TransformationException(i18n("RULE_NOT_NEGATIVE_POSITION"))
      } else {
        throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"))
      }
    }

     if(InferenceTargetExtraction.isLeftOperand(childDiagramIndexArg, compundDiagramIndex)) {
       currentDiagram.getOperand(0)
     } else {
       currentDiagram.getOperand(1)
     }


  }
}
