package speedith.core.reasoning.rules.instructions

import java.util

import speedith.core.reasoning.RuleApplicationInstruction
import speedith.core.reasoning.args.{ZoneArg, SubDiagramIndexArg}
import speedith.core.reasoning.args.selection.{SelectSingleZoneStep, SelectZonesStep, SelectionStep, SelectionSequence}
import scala.collection.JavaConversions._

/**
 * Created by sl542 on 11/11/15.
 */
class SelectSingleZoneInstruction extends RuleApplicationInstruction[ZoneArg]{

  private val steps: List[SelectSingleZoneStep] = List(SelectSingleZoneStep.getInstance())

  def extractRuleArg(selectionSequence: SelectionSequence, subgoalIndex: Int): ZoneArg= {
    val ruleArgs = selectionSequence.getAcceptedSelectionsForStepAt(0)

    val zoneArguments = ruleArgs.map {
      case zoneArg: ZoneArg => new ZoneArg(subgoalIndex, zoneArg.getSubDiagramIndex, zoneArg.getZone)
      case _ => throw new IllegalArgumentException("The target of the inference rule is not a zone.")
    }

    if (zoneArguments.size != 1) throw new IllegalArgumentException("There must be exactly one zone selected.")

    zoneArguments.get(0)
  }

  def getSelectionSteps: util.List[_ <: SelectionStep] = steps

}
