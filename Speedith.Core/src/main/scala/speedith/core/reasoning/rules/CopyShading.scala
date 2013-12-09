package speedith.core.reasoning.rules

import speedith.core.reasoning.args.{ZoneArg, RuleArg}
import speedith.core.reasoning.{InferenceRule, RuleApplicationInstruction, RuleApplicationResult, Goals}
import java.util.Locale
import speedith.core.i18n.Translations
import speedith.core.lang.SpiderDiagram
import scala.collection.JavaConversions._
import speedith.core.reasoning.rules.transformers.CopyShadingTransformer

class CopyShading extends SimpleInferenceRule[ZoneArg] {
  def getInferenceRule: InferenceRule[ZoneArg] = this

  def getInferenceRuleName: String = "copy_shading"

  def getDescription(locale: Locale): String = Translations.i18n(locale, "COPY_SHADING_DESCRIPTION")

  def getPrettyName(locale: Locale): String = Translations.i18n(locale, "COPY_SHADING_PRETTY_NAME")

  def getCategory(locale: Locale): String = Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS")

  def getArgumentType: Class[ZoneArg] = classOf[ZoneArg]

  def getInstructions: RuleApplicationInstruction[ZoneArg] = null

  def apply(args: RuleArg, goals: Goals): RuleApplicationResult = {
    apply(getTypedRuleArgs(args), goals)
  }

  def apply(args: ZoneArg, goals: Goals): RuleApplicationResult = {
    val newSubgoals = goals.getGoals.toList.toArray[SpiderDiagram]
    val targetSubgoal = SimpleInferenceRule.getSubgoal(args, goals)
    val indexOfParent = targetSubgoal.getParentIndexOf(args.getSubDiagramIndex)
    newSubgoals(args.getSubgoalIndex) = targetSubgoal.transform(CopyShadingTransformer(indexOfParent, args))
    new RuleApplicationResult(Goals.createGoalsFrom(seqAsJavaList(newSubgoals)))
  }
}
