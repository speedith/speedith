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
class PrepareCopyShading extends SimpleInferenceTactic with Serializable {
  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = {
    args match {
      case arg: SubgoalIndexArg =>
        BasicTactics.introduceMissingZonesForCopyShading(getPrettyName())(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
          case Some(result) => result.getApplicationList.isEmpty match {
            case false => result
            case true => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
          }
          case None => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
        }
      case _ =>
        throw new RuleApplicationException("Wrong argument type")
    }
  }

  override def getDescription(locale: Locale): String = "Introduces shaded zones in a conjunction suited for copying shading information"

  override def getPrettyName(locale: Locale): String = "Prepare For Copy Shading"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "prepare_copy_shading"

  override def isHighLevel: Boolean = false
}
