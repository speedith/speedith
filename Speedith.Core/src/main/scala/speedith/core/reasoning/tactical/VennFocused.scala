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
class VennFocused extends SimpleInferenceTactic with Serializable{
  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = args match {
    case arg: SubgoalIndexArg =>
      BasicTactics.vennStyleFocused(getPrettyName())(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
        case Some(result) => result.getApplicationList.isEmpty match {
          case false => result
          case true => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
        }
        case None => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
      }
    case _ =>
      throw new RuleApplicationException("Wrong argument type")
  }

  override def getDescription(locale: Locale): String = "Create Venn diagrams and combine as much as possible, then match the premises to the conclusion. Focus one conjunction at a time."

  override def getPrettyName(locale: Locale): String = "Venn (Depth)"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "focused_venn_style"

  override def isHighLevel: Boolean = true
}
