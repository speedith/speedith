package speedith.core.reasoning.rules.transformers

import speedith.core.i18n.Translations._
import speedith.core.lang.{TransformationException, SpiderDiagram, CompoundSpiderDiagram}
import speedith.core.reasoning.ApplyStyle
import speedith.core.reasoning.rules.SimpleInferenceRule
import speedith.core.reasoning.rules.transformers.util.InferenceTargetChecks._

/**
  * TODO: Description
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class DisjunctionEliminationTransformer(compundDiagramIndex : Int, applyStyle: ApplyStyle, operand: Int)
  extends CompoundDiagramTransformer(compundDiagramIndex) {


  override def transform(csd: CompoundSpiderDiagram, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[Integer]): SpiderDiagram = {

    assertIsDisjunction(csd)


    if (!SimpleInferenceRule.isAtFittingPosition(parents, childIndices, applyStyle, true)) {
      if (applyStyle == ApplyStyle.Forward) {
        throw new TransformationException(i18n("RULE_NOT_NEGATIVE_POSITION"))
      } else {
        throw new TransformationException(i18n("RULE_NOT_POSITIVE_POSITION"))
      }
    }

    csd.getOperand(operand)

  }
}
