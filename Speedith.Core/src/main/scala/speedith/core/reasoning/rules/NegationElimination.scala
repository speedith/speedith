package speedith.core.reasoning.rules

import java.util.Locale

import speedith.core.i18n.Translations
import speedith.core.lang._
import speedith.core.lang.util.RegionBuilder.emptyRegion
import speedith.core.lang.util.{HabitatBuilder, HabitatUtils, SpiderUtils}
import speedith.core.reasoning._
import speedith.core.reasoning.args.SubDiagramIndexArg
import speedith.core.reasoning.rules.UnaryForwardRule.UnaryForwardTransformer
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction

import scala.collection.JavaConversions._

class NegationElimination extends UnaryForwardRule with Serializable {

  def getInferenceName: String = "negation_elimination"

  def getDescription(locale: Locale): String = "Negation elimination converts rules of form ¬(UnitaryDiagram) into (UnitaryDiagram || ... || UnitaryDiagram)."

  def getPrettyName(locale: Locale): String = "Negation elimination"

  def getApplicableTypes :  java.util.Set[DiagramType] = Set(DiagramType.SpiderDiagram)

  override def getCategory(locale: Locale): String = Translations.i18n(locale, "INF_RULE_CATEGORY_HETEROGENEOUS")

  override def getArgumentType: Class[SubDiagramIndexArg] = classOf[SubDiagramIndexArg]

  def getInstructions: RuleApplicationInstruction[SubDiagramIndexArg] = {
    new SelectSingleOperatorInstruction(Operator.Negation)
  }

  override protected def getSententialTransformer(arg: SubDiagramIndexArg, applyStyle: ApplyStyle): Transformer = {
    new NegationEliminationTransformer(arg, applyStyle)
  }

  class NegationEliminationTransformer(arg: SubDiagramIndexArg, style: ApplyStyle) extends UnaryForwardTransformer(arg, style) {
    override protected def apply(csd: CompoundSpiderDiagram): SpiderDiagram = {
      if (!csd.getOperand(0).isInstanceOf[PrimarySpiderDiagram] || csd.getOperator != Operator.Negation) {
        unsupported()
      }
      val psd = csd.getOperand(0).asInstanceOf[PrimarySpiderDiagram]
      if (HabitatUtils.zonesToSpiders(psd).values.count(_.nonEmpty) != 1) {
        throw new TransformationException("Elimination negation requires that there must be exactly one zone with some spiders.")
      }
      NegationElimination.apply(psd)
    }

    override protected def unsupported(): SpiderDiagram = {
      throw new TransformationException("Could not apply the 'negation elimination' rule. This rule may be applied only on a negated unitary diagram.")
    }
  }

}

object NegationElimination {
  def apply(diagram: PrimarySpiderDiagram): SpiderDiagram = {
    val spiderHabitat = diagram.getHabitats.values().head
    val spiders = diagram.getSpiders
    val spiderSublists = 0.until(spiders.size).map(spiders.take)
    val firstDisjuncts = spiderSublists.map(spiders => {
      val spiderHabitats = spiders.map((_, spiderHabitat)).toMap
      SpiderDiagrams.createPrimarySD(spiderHabitats, spiderHabitat.sortedZones, diagram.getPresentZones)
    })
    val extraDisjunct = if (diagram.getShadedZones.contains(spiderHabitat.zones.head)) {
      val newSpider = SpiderUtils.freshSpiderName(spiders)
      val newHabitat = new HabitatBuilder(diagram.getHabitats).addHabitat(newSpider, spiderHabitat)
      Some(SpiderDiagrams.createPrimarySD(newHabitat.get(), emptyRegion().asZones(), diagram.getPresentZones))
    } else {
      None
    }
    (firstDisjuncts ++ extraDisjunct).reduceRight(composeConjunctively)
  }

  private def composeConjunctively(lhs: SpiderDiagram, rhs: SpiderDiagram): SpiderDiagram = {
    SpiderDiagrams.createCompoundSD(Operator.Disjunction, lhs, rhs)
  }
}