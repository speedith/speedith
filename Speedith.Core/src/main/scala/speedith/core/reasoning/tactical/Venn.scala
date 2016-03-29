package speedith.core.reasoning.tactical

import java.util
import java.util.Locale

import speedith.core.lang.DiagramType
import speedith.core.reasoning.Goals
import speedith.core.reasoning.args.RuleArg
import scala.collection.JavaConversions._
/**
  * TODO: Description
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class Venn extends SimpleTactic{
  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = ???

  override def getDescription(locale: Locale): String = ???

  override def getPrettyName(locale: Locale): String = ???

  override def getApplicableTypes: util.Set[DiagramType] = Set(DiagramType.EulerDiagram)

  override def getInferenceName: String = ???
}
