package speedith.core.reasoning.rules.instructions

import java.util

import speedith.core.reasoning.RuleApplicationInstruction
import speedith.core.reasoning.args.{MultipleRuleArgs, ZoneArg}
import speedith.core.reasoning.args.selection.{SelectSingleZoneStep, SelectionSequence, SelectionStep}

import scala.collection.JavaConversions._

/**
  * Instruction to select a single zone of a SpiderDiagram.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  */
class SelectSingleZoneInstruction extends RuleApplicationInstruction[MultipleRuleArgs]{

  private val steps: List[SelectSingleZoneStep] = List(SelectSingleZoneStep.getInstance())

  def extractRuleArg(selectionSequence: SelectionSequence, subgoalIndex: Int): MultipleRuleArgs= {
    val ruleArgs = selectionSequence.getAcceptedSelectionsForStepAt(0)

    val zoneArguments = ruleArgs.map {
      case zoneArg: ZoneArg => new ZoneArg(subgoalIndex, zoneArg.getSubDiagramIndex, zoneArg.getZone)
      case _ => throw new IllegalArgumentException("The target of the inference rule is not a zone.")
    }

    if (zoneArguments.size != 1) throw new IllegalArgumentException("There must be exactly one zone selected.")

    new MultipleRuleArgs(zoneArguments.get(0))
  }

  def getSelectionSteps: util.List[_ <: SelectionStep] = steps

}
