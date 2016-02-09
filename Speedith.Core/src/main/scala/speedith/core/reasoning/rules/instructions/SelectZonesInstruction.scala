package speedith.core.reasoning.rules.instructions

import java.util

import speedith.core.reasoning.RuleApplicationInstruction
import speedith.core.reasoning.args.selection.{SelectZonesStep, SelectionSequence, SelectionStep}
import speedith.core.reasoning.args.{MultipleRuleArgs, ZoneArg}

import scala.collection.JavaConversions._

class SelectZonesInstruction extends RuleApplicationInstruction[MultipleRuleArgs] {

  private val steps: List[SelectZonesStep] = List(SelectZonesStep.getInstance())

  def extractRuleArg(selectionSequence: SelectionSequence, subgoalIndex: Int): MultipleRuleArgs = {
    val ruleArgs = selectionSequence.getAcceptedSelectionsForStepAt(0)

    val zoneArguments = ruleArgs.map {
      case zoneArg: ZoneArg => new ZoneArg(subgoalIndex, zoneArg.getSubDiagramIndex, zoneArg.getZone)
      case _ => throw new IllegalArgumentException("The target of the inference rule is not a zone.")
    }

    new MultipleRuleArgs(zoneArguments)
  }

  def getSelectionSteps: util.List[_ <: SelectionStep] = steps
}
