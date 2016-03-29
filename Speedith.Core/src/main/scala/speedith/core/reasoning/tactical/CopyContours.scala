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
class CopyContours extends SimpleTactic {
  override def getDescription(locale: Locale): String = "Copys contours as often as possible"

  override def getPrettyName(locale: Locale): String = "Copy Contours"

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = "copy_contours"

  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = args match {
    case arg: SubgoalIndexArg =>
      SimpleTacticals.copyTopologicalInformation("Copy Contours")(goals)(arg.getSubgoalIndex)(new TacticApplicationResult()) match {
        case Some(result) => result
        case None => throw new TacticApplicationException("Could not apply tactic "+getPrettyName())
      }
    /*        result match {
              case None => throw new RuleApplicationException("Could not unify Contours")
              case Some(newGoals) => new TacticApplicationResult(newGoals)
            }*/
    case _ =>
      throw new RuleApplicationException("Wrong argument type")
  }
}
