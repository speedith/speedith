package speedith.core.reasoning.tactical.euler

import speedith.core.lang._
import speedith.core.reasoning.args._
import speedith.core.reasoning.rules._
import speedith.core.reasoning.tactical.TacticApplicationException
import speedith.core.reasoning.util.unitary.CorrespondingRegions
import speedith.core.reasoning.{ InferenceRule, ProofTrace, Proof}
import speedith.core.reasoning.automatic.wrappers._
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import scala.collection.JavaConversions._
import Auxilliary._

import scala.collection.mutable

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object Tactics {

  private def firstMatchingDiagram(sd : SpiderDiagramOccurrence, predicate : SpiderDiagramOccurrence=> Boolean): Seq[SpiderDiagramOccurrence] = sd match  {
    case sd :CompoundSpiderDiagramOccurrence => {
      if (predicate(sd)) { Seq(sd) } else {
        val matching = firstMatchingDiagram(sd.getOperand(0), predicate)
        matching match {
          case Seq() => firstMatchingDiagram(sd.getOperand(1), predicate)
          case _ => matching
        }
      }
    }
    case sd : PrimarySpiderDiagramOccurrence => {
      if (predicate(sd)) {
        Seq(sd)
      } else {
        Seq()
      }
    }
  }

  private def firstMatchingDiagramAndContour( sd : SpiderDiagramOccurrence,
                                              predicate : SpiderDiagramOccurrence => Boolean,
                                              contourChooser : SpiderDiagramOccurrence => Option[String])
    : Seq[(SpiderDiagramOccurrence, Option[String])] = sd match  {
    case sd : CompoundSpiderDiagramOccurrence => {
      if (predicate(sd)) {Seq(Tuple2(sd, contourChooser(sd)))} else {
        val matching = firstMatchingDiagramAndContour(sd.getOperand(0), predicate, contourChooser)
        matching match {
          case Seq() => firstMatchingDiagramAndContour(sd.getOperand(1), predicate, contourChooser)
          case _ => matching
        }
      }
    }
    case sd : PrimarySpiderDiagramOccurrence => {
      if (predicate(sd)) {
        Seq(Tuple2(sd, contourChooser(sd)))
      } else {
        Seq()
      }
    }
  }



  private def createResults(goals : Seq[SpiderDiagramOccurrence], state : Proof, rule : InferenceRule[RuleArg], args : RuleArg) : Seq[Proof] = {
    val result = goals.map(sd => Tuple2(sd, new ProofTrace(state)))
    val intermediate = result.map(t => t._2.applyRule(rule, args))
    result.map(t => t._2)

  }
  
  def introduceContour(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
   try {
     val subgoal = getSubgoal(subgoalIndex, state)
     val contours = AutomaticUtils.collectContours(subgoal.getDiagram).toSet
     val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
       isPrimaryAndContainsMoreContours(_, contours.toSet))
     if (target.isEmpty) { throw  new TacticApplicationException("No subgoal for this tactic") }
       createResults(target, state, new IntroContour().asInstanceOf[InferenceRule[RuleArg]],
         new MultipleRuleArgs(new ContourArg(subgoalIndex, target.head.getOccurrenceIndex,
           (contours.toSet -- target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours).head)))
   } catch {
     case e : TacticApplicationException => Seq()
   }
 }

  def introduceShadedZone(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isPrimaryAndContainsMissingZones)
      if (target.isEmpty) { throw new TacticApplicationException("No subgoal for this tactic") }
        val missingZones = target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getShadedZones -- target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getPresentZones
        createResults(target, state, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]],
          new ZoneArg(subgoalIndex, target.head.getOccurrenceIndex, missingZones.head))
    } catch {
      case e:TacticApplicationException => Seq()
    }
  }

  def removeShadedZone(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isPrimaryAndContainsShadedZones)
      if (target.isEmpty) { throw new TacticApplicationException("No subgoal for this tactic") }
      val presentShadedZones = target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getShadedZones & target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getPresentZones
      createResults(target, state, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]],
        new ZoneArg(subgoalIndex, target.head.getOccurrenceIndex, presentShadedZones.head))
    } catch {
      case e:TacticApplicationException => Seq()
    }
  }

  def eraseContour(subgoalIndex:Int, predicate: SpiderDiagramOccurrence => Boolean, contourChooser: SpiderDiagramOccurrence => Option[String], state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d => d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(d), contourChooser)
      if (target.isEmpty) {
        throw new TacticApplicationException("No subgoal for this tactic")
      }
      target.head._2 match {
        case Some(c)  =>   {   //val presentContours = target.head.asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours
         createResults (target.map (_._1), state, new RemoveContour ().asInstanceOf[InferenceRule[RuleArg]],
         new MultipleRuleArgs (new ContourArg (subgoalIndex, target.head._1.getOccurrenceIndex, c) ) )
        }
        case None => throw new TacticApplicationException("Could not find a suited contour in this diagram")
      }
    } catch {
      case e: TacticApplicationException => Seq()
    }
  }

  def combine(subgoalIndex: Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
       isConjunctionOfPrimaryDiagramsWithEqualZoneSets)
      if (target.isEmpty) {
        throw new TacticApplicationException("No subgoal for this tactic")
      }
      createResults(target, state, new Combining().asInstanceOf[InferenceRule[RuleArg]],
        new SubDiagramIndexArg(subgoalIndex, target.head.getOccurrenceIndex))
    }catch {
      case e: TacticApplicationException => Seq()
    }
  }

  def copyContour(subgoalIndex: Int,  state: Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionWithContoursToCopy)
      if (target.isEmpty) {
        throw new TacticApplicationException("No subgoal for this tactic")
      }
      val op0 = target.head.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
      val op1 = target.head.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
      if ((op0.getAllContours -- op1.getAllContours).nonEmpty) {
        createResults(Seq(op0),state, new CopyContours().asInstanceOf[InferenceRule[RuleArg]],
        new MultipleRuleArgs (new ContourArg (subgoalIndex, op0.getOccurrenceIndex,(op0.getAllContours -- op1.getAllContours).head ) )  )
      } else {
        createResults(Seq(op1),state, new CopyContours().asInstanceOf[InferenceRule[RuleArg]],
          new MultipleRuleArgs (new ContourArg (subgoalIndex, op1.getOccurrenceIndex,(op1.getAllContours -- op0.getAllContours).head ) )  )
      }
    } catch {
      case e:TacticApplicationException => Seq()
    }
  }

  def copyShading(subgoalIndex : Int, state:Proof) : Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionWithShadingToCopy)
      if (target.isEmpty) {
        throw new TacticApplicationException("No subgoal for this tactic")
      }
      val op0 = target.head.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
      val op1 = target.head.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
      if (op0.getAllContours.subsetOf(op1.getAllContours)) {
        val maxZone = computeMaximalCorrespondingShadedRegion(op0, op1)
        maxZone match {
          case Some((r1: Set[Zone], r2: Set[Zone])) => {
            createResults(Seq(op0), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op0.getOccurrenceIndex, z)).toList))
          }
          case None => {
            if (op1.getAllContours.subsetOf(op0.getAllContours)) {
              val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
              maxZone match {
                case Some((r1: Set[Zone], r2: Set[Zone])) => {
                  createResults(Seq(op1), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                    new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op1.getOccurrenceIndex, z)).toList))
                }
                case None => Seq()
              }
            } else Seq()
          }
        }
      } else if (op1.getAllContours.subsetOf(op0.getAllContours)) {
        val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
        maxZone match {
          case Some((r1: Set[Zone], r2: Set[Zone])) => {
            createResults(Seq(op1), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op1.getOccurrenceIndex, z)).toList))
          }
          case None => Seq()
        }
      } else Seq()
    }catch {
      case e:TacticApplicationException => Seq()
    }
  }


  def trivialTautology(subgoalIndex: Int, state: Proof): Seq[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal,isImplication)
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
  private def getSubgoal( subgoalIndex : Int, state:Proof ): SpiderDiagramOccurrence  = {
    if (!state.isFinished) {
      val goal = state.getLastGoals.getGoalAt(subgoalIndex)
      if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
        SpiderDiagramOccurrence.wrapDiagram(goal, 0)
      } else throw new TacticApplicationException("No subgoal for this tactic")
    } else throw new TacticApplicationException("No subgoal for this tactic")
  }
}


