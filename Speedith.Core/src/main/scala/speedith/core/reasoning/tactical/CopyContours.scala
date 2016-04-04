package speedith.core.reasoning.tactical

import java.util
import java.util.Locale

import speedith.core.lang.DiagramType
import speedith.core.reasoning.{RuleApplicationException, Goals}
import speedith.core.reasoning.args.{SubgoalIndexArg, RuleArg}
import speedith.core.reasoning.tactical.euler.SimpleTacticals
import scala.collection.JavaConversions._
/**
  * TODO: Description
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class CopyContours extends SimpleTactic with Serializable {
  override def getDescription(locale: Locale): String = "Copys contours as often as possible"

  override def getPrettyName(locale: Locale): String = "Copy Contours"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "copy_contours"

  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = args match {
    case arg: SubgoalIndexArg =>
      SimpleTacticals.copyTopologicalInformation(getPrettyName())(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
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