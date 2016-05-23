package speedith.core.reasoning.rules



import java.util.Locale

import speedith.core.i18n.Translations
import speedith.core.lang.{DiagramType, SpiderDiagram}
import speedith.core.reasoning.args.{RuleArg, SpiderArg}
import speedith.core.reasoning.rules.instructions.SelectSpiderInstruction
import speedith.core.reasoning.rules.transformers.CopySpiderTransformer
import speedith.core.reasoning.{Goals, InferenceRule, RuleApplicationInstruction, RuleApplicationResult}

import scala.collection.JavaConversions._

class CopySpider extends SimpleInferenceRule[SpiderArg] with Serializable {
  def getInferenceRule: InferenceRule[SpiderArg] = {
    this
  }

  def getInferenceName: String = "copy_spider"

  def getApplicableTypes: java.util.Set[DiagramType] = Set(DiagramType.SpiderDiagram)

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
    val newSubgoals = goals.getGoals.toSeq.toArray[SpiderDiagram]
    val targetSubgoal = SimpleInferenceRule.getSubgoal(args, goals)
    val indexOfParent: Int = targetSubgoal.getParentIndexOf(args.getSubDiagramIndex)
    newSubgoals(args.getSubgoalIndex) = targetSubgoal.transform(CopySpiderTransformer(indexOfParent, args))
    new RuleApplicationResult(Goals.createGoalsFrom(seqAsJavaList(newSubgoals)))
  }
}
