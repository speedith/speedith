package speedith.core.reasoning.rules

import java.util.Locale

import speedith.core.i18n.Translations
import speedith.core.lang._
import speedith.core.reasoning._
import speedith.core.reasoning.args.SubDiagramIndexArg
import speedith.core.reasoning.rules.UnaryForwardRule.UnaryForwardTransformer
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction

class NegationElimination extends UnaryForwardRule {

  def getInferenceRuleName: String = "negation_elimination"

  def getDescription(locale: Locale): String = "Negation elimination converts rules of form ¬(UnitaryDiagram) into (UnitaryDiagram || ... || UnitaryDiagram)."

  def getPrettyName(locale: Locale): String = "Negation elimination"

  override def getCategory(locale: Locale): String = Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS")

  override def getArgumentType: Class[SubDiagramIndexArg] = classOf[SubDiagramIndexArg]

  def getInstructions: RuleApplicationInstruction[SubDiagramIndexArg] = {
    new SelectSingleOperatorInstruction(Operator.Negation)
  }

  override protected def getSententialTransformer(arg: SubDiagramIndexArg, applyStyle: ApplyStyle): Transformer = {
    new NegationEliminationTransformer(arg, applyStyle)
  }

  class NegationEliminationTransformer(arg: SubDiagramIndexArg, style: ApplyStyle) extends UnaryForwardTransformer(arg, style) {
    override protected def apply(sd: CompoundSpiderDiagram): SpiderDiagram = {
      sd
    }

    override protected def unsupported(): SpiderDiagram = {
      throw new TransformationException("Could not apply the 'negation elimination' rule. This rule may be applied only on a negated unitary diagram.")
    }
  }

}
