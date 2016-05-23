package speedith.core.reasoning.tactical

import java.util
import java.util.Locale

import speedith.core.lang.DiagramType
import speedith.core.reasoning.{RuleApplicationException, Goals}
import speedith.core.reasoning.args.{SubgoalIndexArg, RuleArg}
import speedith.core.reasoning.tactical.euler.BasicTactics
import scala.collection.JavaConversions._
/**
  * TODO: Description
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class DeVennify extends SimpleInferenceTactic with Serializable{
  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = args match {
    case arg: SubgoalIndexArg =>
      BasicTactics.deVennify(getPrettyName())(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
        case Some(result) => result.getApplicationList.isEmpty match {
          case false => result
          case true => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
        }
        case None => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
      }
    case _ =>
      throw new RuleApplicationException("Wrong argument type")
  }

  override def getDescription(locale: Locale): String = "Removes the shaded zones in all diagrams in the premises"

  override def getPrettyName(locale: Locale): String = "Remove All Shaded Zones"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "devennify"

  override def isHighLevel: Boolean = false
}
