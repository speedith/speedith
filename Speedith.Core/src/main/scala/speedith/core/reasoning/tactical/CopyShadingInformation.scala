package speedith.core.reasoning.tactical

import java.util
import java.util.Locale

import speedith.core.lang.DiagramType
import speedith.core.reasoning.{RuleApplicationException, Goals}
import speedith.core.reasoning.args.{SubgoalIndexArg, RuleArg}
import speedith.core.reasoning.tactical.euler.BasicTactics
import scala.collection.JavaConversions._
/**
  * Integration of scala Copy Shading InferenceTactic into Speedith reasoning framework.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class CopyShadingInformation extends SimpleInferenceTactic with Serializable {

  override def getPrettyName(locale: Locale): String = "Propagate Shading"

  override def getDescription(locale: Locale): String = "Introduce shaded zones and copy as much shading as possible"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "copy_shadings"

  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = args match {
    case arg: SubgoalIndexArg =>
      BasicTactics.copyShadings(getPrettyName())(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
        case Some(result) => result.getApplicationList.isEmpty match {
          case false => result
          case true => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
        }
        case None => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
      }
    case _ =>
      throw new RuleApplicationException("Wrong argument type")
  }

  override def isHighLevel: Boolean = true
}
