package speedith.core.reasoning.tactical

import speedith.core.reasoning.{RuleApplicationException, Goals}
import speedith.core.reasoning.args.{SubgoalIndexArg, RuleArg}
import speedith.core.reasoning.tactical.euler.SimpleTacticals

/**
  * TODO: Description
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
class UnifyContours extends SimpleTactic {
  override def apply(args: RuleArg, goals: Goals): TacticApplicationResult = {
    args match {
      case arg: SubgoalIndexArg =>
         SimpleTacticals.unifyContourSets("Unify Contours")(goals)(arg.getSubgoalIndex)(new TacticApplicationResult(goals))
/*        result match {
          case None => throw new RuleApplicationException("Could not unify Contours")
          case Some(newGoals) => new TacticApplicationResult(newGoals)
        }*/
      case _ =>
        throw new RuleApplicationException("Wrong argument type")
    }
  }
}
