package speedith.core.reasoning.tactical.euler

import speedith.core.lang.{TransformationException, SpiderDiagram, Operator, CompoundSpiderDiagram}
import speedith.core.reasoning.args._
import speedith.core.reasoning.rules.{RemoveShadedZone, TrivialImplicationTautology, IntroShadedZone, IntroContour}
import speedith.core.reasoning.tactical.TacticApplicationException
import speedith.core.reasoning.{RuleApplicationException, InferenceRule, ProofTrace, Proof}
import speedith.core.reasoning.automatic.AutomaticProver
import speedith.core.reasoning.automatic.wrappers.{PrimarySpiderDiagramWrapper, CompoundSpiderDiagramWrapper, SpiderDiagramWrapper}
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import scala.collection.JavaConversions._

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object Tactics {

  private def firstMatchingDiagram(sd : SpiderDiagramWrapper, predicate : SpiderDiagramWrapper=> Boolean): Seq[SpiderDiagramWrapper] = sd match  {
    case sd :CompoundSpiderDiagramWrapper => {
      if (predicate(sd)) { Seq(sd) } else {
        val matching = firstMatchingDiagram(sd.getOperand(0), predicate)
        matching match {
          case Seq() => firstMatchingDiagram(sd.getOperand(1), predicate)
          case _ => matching
        }
      }
    }
    case sd : PrimarySpiderDiagramWrapper => {
      if (predicate(sd)) {
        Seq(sd)
      } else {
        Seq()
      }
    }
  }

  private def isPrimaryAndContainsMoreContours(sd : SpiderDiagramWrapper, contours : Set[String]) : Boolean = sd match {
    case sd:PrimarySpiderDiagramWrapper => (contours -- sd.getAllContours).nonEmpty
    case _ => false
  }

  private def isPrimaryAndContainsMissingZones(sd : SpiderDiagramWrapper) : Boolean = sd match {
    case sd:PrimarySpiderDiagramWrapper => (sd.getShadedZones--sd.getPresentZones).nonEmpty
    case _ => false
  }

  private def isPrimaryAndContainsShadedZones(sd : SpiderDiagramWrapper) : Boolean = sd match {
    case sd:PrimarySpiderDiagramWrapper => (sd.getShadedZones & sd.getPresentZones).nonEmpty
    case _ => false
  }

  private def createResults(goals : Seq[SpiderDiagramWrapper], state : Proof, rule : InferenceRule[RuleArg], args : RuleArg) : Seq[Proof] = {
    val result = goals.map(sd => Tuple2(sd, new ProofTrace(state)))
    val intermediate = result.map(t => t._2.applyRule(rule, args))
    result.map(t => t._2)
  }
  
 def introduceContour(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
   try {
     val subgoal = getSubgoal(subgoalIndex, state)
     val contours = AutomaticUtils.collectContours(subgoal.getDiagram)
     val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramWrapper].getOperand(0),
       isPrimaryAndContainsMoreContours(_, contours.toSet))
     if (target.isEmpty) { throw  new TacticApplicationException("No subgoal for this tactic") }
       createResults(target, state, new IntroContour().asInstanceOf[InferenceRule[RuleArg]],
         new MultipleRuleArgs(new ContourArg(subgoalIndex, target.head.getOccurrenceIndex,
           (contours.toSet -- target.head.asInstanceOf[PrimarySpiderDiagramWrapper].getAllContours).head)))
   } catch {
     case e : TacticApplicationException => Seq()
   }
 }
  def introduceShadedZone(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramWrapper].getOperand(0),
        isPrimaryAndContainsMissingZones)
      if (target.isEmpty) { throw new TacticApplicationException("No subgoal for this tactic") }
        val missingZones = target.head.asInstanceOf[PrimarySpiderDiagramWrapper].getShadedZones -- target.head.asInstanceOf[PrimarySpiderDiagramWrapper].getPresentZones
        createResults(target, state, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]],
          new ZoneArg(subgoalIndex, target.head.getOccurrenceIndex, missingZones.head))
    } catch {
      case e:TacticApplicationException => Seq()
    }
  }

  def removeShadedZone(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramWrapper].getOperand(0),
        isPrimaryAndContainsShadedZones)
      if (target.isEmpty) { throw new TacticApplicationException("No subgoal for this tactic") }
      val presentShadedZones = target.head.asInstanceOf[PrimarySpiderDiagramWrapper].getShadedZones & target.head.asInstanceOf[PrimarySpiderDiagramWrapper].getPresentZones
      createResults(target, state, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]],
        new ZoneArg(subgoalIndex, target.head.getOccurrenceIndex, presentShadedZones.head))
    } catch {
      case e:TacticApplicationException => Seq()
    }
  }

  private def isCompoundAndAnImplication (sd : SpiderDiagramWrapper): Boolean = sd match {
    case sd:CompoundSpiderDiagramWrapper => sd.getOperator match {
      case Operator.Implication => true
      case _ => false
    }
    case _ => false
  }

  def trivialTautology(subgoalIndex: Int, state: Proof): Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal,isCompoundAndAnImplication)
      if (target.isEmpty) {
        throw new TacticApplicationException("No subgoal for this tactic")
      }
      createResults(target, state, new TrivialImplicationTautology().asInstanceOf[InferenceRule[RuleArg]],
        new SubDiagramIndexArg(subgoalIndex, target.head.getOccurrenceIndex))
    }
    catch {
      case e: TacticApplicationException => Seq()
      case e: TransformationException => Seq()
    }
  }

  /**
   * implements some general checks
   *
   * @param subgoalIndex the index of subgoal which shall be returned
   * @param state the proof from in which the subgoal will be searched
   */
  private def getSubgoal( subgoalIndex : Int, state:Proof ): SpiderDiagramWrapper  = {
    if (!state.isFinished) {
      val goal = state.getLastGoals.getGoalAt(subgoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        AutomaticProver.wrapDiagram(goal, 0)
      } else throw new TacticApplicationException("No subgoal for this tactic")
    } else throw new TacticApplicationException("No subgoal for this tactic")
  }
}


