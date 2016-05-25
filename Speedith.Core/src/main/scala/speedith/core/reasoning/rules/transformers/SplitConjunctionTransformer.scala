package speedith.core.reasoning.rules.transformers



import speedith.core.i18n.Translations._
import speedith.core.lang.{TransformationException, SpiderDiagram, CompoundSpiderDiagram}
import speedith.core.reasoning.ApplyStyle

import speedith.core.reasoning.rules.SimpleInferenceRule
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._


/**
  * Transforms a Spider diagram into a diagram, where the selected conjunction is replaced
  * by one of the conjuncts. This transformer should be used twice, to create one subgoal for each
  * operand (during backwards reasoning)
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class SplitConjunctionTransformer(compundDiagramIndex : Int, applyStyle: ApplyStyle, operand: Int)
  extends CompoundDiagramTransformer(compundDiagramIndex) {


  override def transform(csd: CompoundSpiderDiagram, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[Integer]): SpiderDiagram = {

    assertIsConjunction(csd)


    if (!SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, false)) {
      if (applyStyle == ApplyStyle.Forward) {
        throw new TransformationException(i18n("RULE_NOT_NEGATIVE_POSITION"))
      } else {
        throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"))
      }
    }

    csd.getOperand(operand)
  }

}
