package speedith.core.reasoning.rules

import speedith.core.reasoning.args.{ContourArg, RuleArg, SpiderArg}
import speedith.core.reasoning.{InferenceRule, RuleApplicationInstruction, RuleApplicationResult, Goals}
import java.util.Locale
import speedith.core.i18n.Translations
import speedith.core.lang.SpiderDiagram
import scala.collection.JavaConversions._
import speedith.core.reasoning.rules.transformers.CopySpiderTransformer
import speedith.core.reasoning.rules.instructions.SelectSpiderInstruction

class CopySpider extends SimpleInferenceRule[SpiderArg] {
  def getInferenceRule: InferenceRule[SpiderArg] = {
    this
  }

  def getInferenceRuleName: String = "copy_spider"

  def getDescription(locale: Locale): String = Translations.i18n(locale, "COPY_SPIDER_DESCRIPTION")

  def getPrettyName(locale: Locale): String = Translations.i18n(locale, "COPY_SPIDER_PRETTY_NAME")

  def getCategory(locale: Locale): String = Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS")

  def getArgumentType: Class[SpiderArg] = classOf[SpiderArg]

  def getInstructions: RuleApplicationInstruction[SpiderArg] = {
    new SelectSpiderInstruction()
  }

  def apply(args: RuleArg, goals: Goals): RuleApplicationResult = {
    apply(getTypedRuleArgs(args), goals)
  }

  def apply(args: SpiderArg, goals: Goals): RuleApplicationResult = {
    val newSubgoals = goals.getGoals.toList.toArray[SpiderDiagram]
    val targetSubgoal = SimpleInferenceRule.getSubgoal(args, goals)
    val indexOfParent: Int = targetSubgoal.getParentIndexOf(args.getSubDiagramIndex)
    newSubgoals(args.getSubgoalIndex) = targetSubgoal.transform(CopySpiderTransformer(indexOfParent, args))
    new RuleApplicationResult(Goals.createGoalsFrom(seqAsJavaList(newSubgoals)))
  }
}
