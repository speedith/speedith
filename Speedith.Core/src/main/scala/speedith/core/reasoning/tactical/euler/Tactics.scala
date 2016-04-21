package speedith.core.reasoning.tactical.euler

import speedith.core.lang._
import speedith.core.reasoning.args._
import speedith.core.reasoning.automatic.wrappers._
import speedith.core.reasoning.rules._
import speedith.core.reasoning.rules.util.{AutomaticUtils, ReasoningUtils}
import speedith.core.reasoning.tactical.{TacticApplicationResult, TacticApplicationException}
import speedith.core.reasoning.tactical.euler.Auxilliary._
import speedith.core.reasoning.tactical.euler.Predicates._

import speedith.core.reasoning._


import scala.collection.JavaConversions._

/**
  * Contains the main tactics to apply single rules to a given proof.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object Tactics {

  private def firstMatchingDiagram(sd: SpiderDiagramOccurrence, predicate: Predicate): Option[SpiderDiagramOccurrence] = {
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
                                             contourChooser: Chooser[Set[String]])
  : Option[(SpiderDiagramOccurrence, Option[Set[String]])] = {
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


  private def createResults(goals: Goals, rule: InferenceRule[RuleArg], args: RuleArg, name : String, oldResult : TacticApplicationResult): Option[TacticApplicationResult] =  {
      val result = rule.apply(args, goals)
      val app = new InferenceApplication(rule, args, RuleApplicationType.TACTIC, name)
      val newGoals = result.getGoals.getGoals.filterNot(d => NullSpiderDiagram.getInstance().isSEquivalentTo(d))
      val newGoal = Goals.createGoalsFrom(newGoals)
       Some(new TacticApplicationResult(oldResult.getApplicationList :+ app, newGoal))
  }

  def introduceContour(predicate : Predicate , contourChooser: Chooser[Set[String]]):Tactical = (name:String) => (state: Goals) => (subGoalIndex:Int) =>(result : TacticApplicationResult) =>{
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d=> d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(d), contourChooser )
      target match {
        case None => None
        case Some(tupel) =>
          tupel._2 match {
            case Some(c) =>
              createResults(state, new IntroContour().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(c.map(new ContourArg(subGoalIndex, tupel._1.getOccurrenceIndex, _)).toSeq: _*
                ), name, result)
            case None => None
          }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def introduceShadedZone(predicate: Goals => Predicate, zoneChooser : Chooser[Set[Zone]]): Tactical =
    (name:String) =>(state: Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d => d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(state)(d))
      target match {
        case None => None
        case Some(diagram) =>
          val targetZones = zoneChooser(diagram)
          targetZones match {
            case Some(zones) =>
              createResults(state, new IntroShadedZone().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(zones.map( zone =>new ZoneArg(subGoalIndex, diagram.getOccurrenceIndex, zone)).toSeq:_*),
                name, result)
            case None => None
          }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def   removeShadedZone(zoneChooser:Chooser[Set[Zone]]): Tactical = (name:String) => ( state: Goals) => (subGoalIndex:Int) =>(result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isPrimaryAndContainsShadedZones)
      target match {
        case None => None
        case Some(diagram) =>
          val targetZone = zoneChooser(diagram)
          targetZone match {
            case Some(zones) =>
              if (zones.exists(_.getInContoursCount == 0)) {
                throw new TacticApplicationException("Cannot remove outer zone")
              }
              createResults(state, new RemoveShadedZone().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(zones.map( z => new ZoneArg(subGoalIndex, diagram.getOccurrenceIndex, z)).toSeq:_*),
                name, result)
            case None => None
          }

      }
    } catch {
      case e: TacticApplicationException => None
      case e: RuleApplicationException => None
    }
  }

  def eraseContour(predicate: Predicate, contourChooser: Chooser[Set[String]]): Tactical =
    (name:String) =>(state: Goals) => (subGoalIndex : Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        d => d.isInstanceOf[PrimarySpiderDiagramOccurrence] && predicate(d), contourChooser)
      target match {
        case Some(tupel) =>
          tupel._2 match {
            case Some(c) =>
              createResults(state, new RemoveContour().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(c.map( new ContourArg(subGoalIndex, tupel._1.getOccurrenceIndex, _)).toSeq:_*),
                name, result)
            case None => throw new TacticApplicationException("Could not find a suited contour in this diagram")
          }
        case None => None
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def eraseShading(predicate: Predicate, zoneChooser : Chooser[Set[Zone]]) :  Tactical  =
    (name:String) =>(state : Goals) => (subGoalIndex : Int) => (result:TacticApplicationResult) =>  {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0), predicate)
      target match {
        case Some(diagram) =>
          val targetZone = zoneChooser(diagram)
          targetZone match {
            case Some(zones) =>
              createResults(state, new RemoveShading().asInstanceOf[InferenceRule[RuleArg]],
                new MultipleRuleArgs(zones.map(zone => new ZoneArg(subGoalIndex, diagram.getOccurrenceIndex, zone)).toSeq:_*),
                name, result)
            case None => None
          }
        case None => None
      }
    } catch {
      case e : TacticApplicationException => None
    }
  }

  def combine: Tactical = (name:String) =>(state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionOfPrimaryDiagramsWithEqualZoneSets)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(state, new Combining().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex),name, result)
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }

  def copyContour: Tactical = (name:String) =>(state: Goals) => (subGoalIndex: Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        isConjunctionWithContoursToCopy)
      target match {
        case None => None
        case Some(diagram) =>
          val op0 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0).asInstanceOf[PrimarySpiderDiagramOccurrence]
          val op1 = diagram.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(1).asInstanceOf[PrimarySpiderDiagramOccurrence]
          if ((op0.getAllContours -- op1.getAllContours).nonEmpty) {
            createResults(state, new CopyContoursTopological().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(new ContourArg(subGoalIndex, op0.getOccurrenceIndex, (op0.getAllContours -- op1.getAllContours).head)),name, result)
          } else {
            createResults(state, new CopyContoursTopological().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(new ContourArg(subGoalIndex, op1.getOccurrenceIndex, (op1.getAllContours -- op0.getAllContours).head)),name,result)
          }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }


  def copyShading : Tactical =
    (name:String) => (state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
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
                createResults(state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                  new MultipleRuleArgs(r1.map(z => new ZoneArg(subGoalIndex, op0.getOccurrenceIndex, z)).toList),
                  name, result)
              case None =>
                if (op1.getAllContours.subsetOf(op0.getAllContours)) {
                  val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
                  maxZone match {
                    case Some((r1: Set[Zone], r2: Set[Zone])) =>
                      createResults(state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                        new MultipleRuleArgs(r1.map(z => new ZoneArg(subGoalIndex, op1.getOccurrenceIndex, z)).toList),
                        name, result)
                    case None => None
                  }
                } else None
            }
          } else if (op1.getAllContours.subsetOf(op0.getAllContours)) {
            val maxZone = computeMaximalCorrespondingShadedRegion(op1, op0)
            maxZone match {
              case Some((r1: Set[Zone], r2: Set[Zone])) =>
                createResults(state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                  new MultipleRuleArgs(r1.map(z => new ZoneArg(subGoalIndex, op1.getOccurrenceIndex, z)).toList),
                  name, result)
              case None => None
            }
          } else None
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }


  def idempotency : Tactical = (name:String) => ( state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal, isIdempotent)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(state, new Idempotency().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex),name, result)
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }

  def trivialTautology :  Tactical = (name:String) =>( state: Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal, isImplication)
      target match {
        case None => None
        case Some(diagram) =>
          createResults(state, new TrivialImplicationTautology().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex),name, result)
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }


}


