package speedith.core.reasoning.tactical.euler

import speedith.core.lang._
import speedith.core.reasoning.args._
import speedith.core.reasoning.automatic.wrappers._
import speedith.core.reasoning.rules._
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import speedith.core.reasoning.tactical.TacticApplicationException
import speedith.core.reasoning.tactical.euler.Auxilliary._
import speedith.core.reasoning._

import scala.collection.JavaConversions._

/**
  * Contains the main tactics to apply single rules to a given proof.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object Tactics {

  private def firstMatchingDiagram(sd: SpiderDiagramOccurrence, predicate: SpiderDiagramOccurrence => Boolean): Option[SpiderDiagramOccurrence] = {
    if (predicate(sd)) {
      Some(sd)
    } else {
      sd match {
        case sd: CompoundSpiderDiagramOccurrence =>
          val matching = firstMatchingDiagram(sd.getOperand(0), predicate)
          matching match {
            case None => firstMatchingDiagram(sd.getOperand(1), predicate)
            case _ => matching
          }
        case sd: PrimarySpiderDiagramOccurrence => None
      }
    }
  }

  private def firstMatchingDiagramAndContour(sd: SpiderDiagramOccurrence,
                                             predicate: SpiderDiagramOccurrence => Boolean,
                                             contourChooser: SpiderDiagramOccurrence => Option[String])
  : Option[(SpiderDiagramOccurrence, Option[String])] = {
    if (predicate(sd)) {
      Some(Tuple2(sd, contourChooser(sd)))
    } else {
      sd match {
        case sd: CompoundSpiderDiagramOccurrence =>
          val matching = firstMatchingDiagramAndContour(sd.getOperand(0), predicate, contourChooser)
          matching match {
            case None => firstMatchingDiagramAndContour(sd.getOperand(1), predicate, contourChooser)
            case _ => matching
          }
        case sd: PrimarySpiderDiagramOccurrence => None
      }
    }
  }


  private def createResults(goals: Option[SpiderDiagramOccurrence], state: Proof, rule: InferenceRule[RuleArg], args: RuleArg): Option[Proof] = goals match {
    case None => None
    case Some(diagram) =>
      val result = Tuple2(diagram, new ProofTrace(state))
      // intermediate is used to create the rule applications (applyRule changes the given proof and
      // returns a RuleApplicationResult!)
      val intermediate = result._2.applyRule(rule, args, RuleApplicationType.TACTIC)
      Some(result._2)
  }

  def introduceContour(subgoalIndex: Int, state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val contours = AutomaticUtils.collectContours(subgoal.getDiagram).toSet
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isPrimaryAndContainsMoreContours(_, contours.toSet))
      target match {
        case None => None
        case Some(diagram) =>
          createResults(target, state, new IntroContour().asInstanceOf[InferenceRule[RuleArg]],
            new MultipleRuleArgs(new ContourArg(subgoalIndex, diagram.getOccurrenceIndex,
              (contours.toSet -- diagram.asInstanceOf[PrimarySpiderDiagramOccurrence].getAllContours).head)))
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def introduceShadedZone(subgoalIndex: Int, predicate: SpiderDiagramOccurrence => Proof => Boolean, zoneChooser : SpiderDiagramOccurrence => Option[Zone],  state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d => d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(d)(state))
      target match {
        case None => None
        case Some(diagram) => {
          val targetZone = zoneChooser(diagram)
          targetZone match {
            case Some(zone) =>
              createResults(target, state, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]],
                new ZoneArg(subgoalIndex, diagram.getOccurrenceIndex, zone))
            case None => None
          }
        }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def removeShadedZone(subgoalIndex: Int, zoneChooser: SpiderDiagramOccurrence => Option[Zone], state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isPrimaryAndContainsShadedZones)
      target match {
        case None => None
        case Some(diagram) =>
//          val presentShadedZones = diagram.asInstanceOf[PrimarySpiderDiagramOccurrence].getShadedZones & diagram.asInstanceOf[PrimarySpiderDiagramOccurrence].getPresentZones
          val targetZone = zoneChooser(diagram)
          targetZone match {
            case Some(zone) =>
              if (zone.getInContoursCount == 0) {
                throw new TacticApplicationException("Cannot remove outer zone")
              }
              createResults(target, state, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]],
                new ZoneArg(subgoalIndex, diagram.getOccurrenceIndex, zone))
            case None => None
          }

      }
    } catch {
      case e: TacticApplicationException => None
      case e: RuleApplicationException => None
    }
  }

  def eraseContour(subgoalIndex: Int, predicate: SpiderDiagramOccurrence => Boolean, contourChooser: SpiderDiagramOccurrence => Option[String], state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d => d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(d), contourChooser)
      target match {
        case Some(tupel) =>
          tupel._2 match {
            case Some(c) =>
              createResults(Some(tupel._1), state, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(new ContourArg(subgoalIndex, tupel._1.getOccurrenceIndex, c)))
            case None => throw new TacticApplicationException("Could not find a suited contour in this diagram")
          }
        case None => None
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def combine(subgoalIndex: Int, state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionOfPrimaryDiagramsWithEqualZoneSets)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(target, state, new Combining().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subgoalIndex, diagram.getOccurrenceIndex))
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def copyContour(subgoalIndex: Int, state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionWithContoursToCopy)
      target match {
        case None => None
        case Some(diagram) =>
          val op0 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op1 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          if ((op0.getAllContours -- op1.getAllContours).nonEmpty) {
            createResults(Some(op0), state, new CopyContoursTopological().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(new ContourArg(subgoalIndex, op0.getOccurrenceIndex, (op0.getAllContours -- op1.getAllContours).head)))
          } else {
            createResults(Some(op1), state, new CopyContoursTopological().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(new ContourArg(subgoalIndex, op1.getOccurrenceIndex, (op1.getAllContours -- op0.getAllContours).head)))
          }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def copyShading(subgoalIndex: Int, state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionWithShadingToCopy)
      target match {
        case None => None
        case Some(diagram) =>
          val op0 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op1 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          if (op0.getAllContours.subsetOf(op1.getAllContours)) {
            val maxZone = computeMaximalCorrespondingShadedRegion(op0, op1)
            maxZone match {
              case Some((r1: Set[Zone], r2: Set[Zone])) =>
                createResults(Some(op0), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                  new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op0.getOccurrenceIndex, z)).toList))
              case None =>
                if (op1.getAllContours.subsetOf(op0.getAllContours)) {
                  val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
                  maxZone match {
                    case Some((r1: Set[Zone], r2: Set[Zone])) =>
                      createResults(Some(op1), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                        new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op1.getOccurrenceIndex, z)).toList))
                    case None => None
                  }
                } else None
            }
          } else if (op1.getAllContours.subsetOf(op0.getAllContours)) {
            val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
            maxZone match {
              case Some((r1: Set[Zone], r2: Set[Zone])) =>
                createResults(Some(op1), state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                  new MultipleRuleArgs(r1.map(z => new ZoneArg(subgoalIndex, op1.getOccurrenceIndex, z)).toList))
              case None => None
            }
          } else None
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def idempotency(subGoalIndex : Int, state:Proof) : Option[Proof] = {
    try {
      val subgoal = getSubgoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal, isIdempotent)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(target, state, new Idempotency().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex))
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }


  def trivialTautology(subgoalIndex: Int, state: Proof): Option[Proof] = {
    try {
      val subgoal = getSubgoal(subgoalIndex, state)
      val target = firstMatchingDiagram(subgoal, isImplication)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(target, state, new TrivialImplicationTautology().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subgoalIndex, diagram.getOccurrenceIndex))
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }


}


