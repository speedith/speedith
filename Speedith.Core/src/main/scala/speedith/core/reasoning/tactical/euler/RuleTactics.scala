package speedith.core.reasoning.tactical.euler

import speedith.core.lang._
import speedith.core.reasoning.args._
import speedith.core.reasoning.automatic.wrappers._
import speedith.core.reasoning.rules._
import speedith.core.reasoning.tactical.{Chooser, TacticApplicationResult, TacticApplicationException, DiagramPredicate, Tactic}
import speedith.core.reasoning.tactical.euler.Auxiliary._
import speedith.core.reasoning.tactical.euler.Predicates._
import speedith.core.reasoning.tactical._
import speedith.core.reasoning._

import scala.collection.JavaConversions._

/**
  * Contains the main tactics to apply single rules to a given proof. The targets of these tactics
  * have to be specificed by suited Predicate and Chooser[A] functions.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object RuleTactics {

  private def createResults(goals: Goals, rule: InferenceRule[RuleArg], args: RuleArg, name : String, oldResult : TacticApplicationResult): Option[TacticApplicationResult] =  {
      val result = rule.apply(args, goals)
      val app = new InferenceApplication(rule, args, RuleApplicationType.TACTIC, name)
      val newGoals = result.getGoals.getGoals.filterNot(d => NullSpiderDiagram.getInstance().isSEquivalentTo(d))
      val newGoal = Goals.createGoalsFrom(newGoals)
       Some(new TacticApplicationResult(oldResult.getApplicationList :+ app, newGoal))
  }

  def introduceContour(predicate : DiagramPredicate, contourChooser: Chooser[Set[String]]):Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int) => (result : TacticApplicationResult) =>{
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
          predicate, contourChooser )
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

  def introduceShadedZone(predicate: DiagramPredicate, zoneChooser : Chooser[Set[Zone]]): Tactic =
    (name:String) =>(state: Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0), predicate)
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

  def removeShadedZone(predicate : DiagramPredicate, zoneChooser:Chooser[Set[Zone]]): Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        predicate)
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

  def eraseContour(predicate: DiagramPredicate, contourChooser: Chooser[Set[String]]): Tactic =
    (name:String) =>(state: Goals) => (subGoalIndex : Int) => (result:TacticApplicationResult) => {
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagramAndContour(subgoal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0),
        predicate, contourChooser)
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

  def eraseShading(predicate: DiagramPredicate, zoneChooser : Chooser[Set[Zone]]) :  Tactic  =
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

  def combine: Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
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

  def copyContour: Tactic = (name:String) => (state: Goals) => (subGoalIndex: Int) => (result:TacticApplicationResult) => {
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


  def copyShading : Tactic =
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
          val leftToRight = getCorrespondingShadedRegion(op0,op1)
          leftToRight match {
            case Some((r1: Set[Zone], r2: Set[Zone])) => createResults(state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
              new MultipleRuleArgs(r1.map(z => new ZoneArg(subGoalIndex, op0.getOccurrenceIndex, z)).toList),
              name, result)
            case None =>
                val rightToLeft = getCorrespondingShadedRegion(op1,op0)
              rightToLeft match {
                case Some((r1: Set[Zone], r2: Set[Zone])) =>
                  createResults(state, new CopyShading().asInstanceOf[InferenceRule[RuleArg]],
                    new MultipleRuleArgs(r1.map(z => new ZoneArg(subGoalIndex, op1.getOccurrenceIndex, z)).toList),
                    name, result)
                case None => None
              }
          }
      }
    } catch {
      case e: TacticApplicationException => None
    }
  }


  def idempotency : Tactic = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
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

  def trivialTautology :  Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
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


  def splitConjunction :  Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal, AND(isConjunction,isAtPositivePosition(subgoal)))
      target match {
        case None => None
        case Some(diagram) =>
          createResults(state, new SplitConjunction().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex),name, result)
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }

  def splitDisjunction:  Tactic = (name:String) => (state: Goals) => (subGoalIndex:Int)=> (result : TacticApplicationResult) =>{
    try {
      val subgoal = getSubGoal(subGoalIndex, state)
      val target = firstMatchingDiagram(subgoal, AND(isDisjunction,isAtNegativePosition(subgoal)))
      target match {
        case None => None
        case Some(diagram) =>
          createResults(state, new SplitDisjunction().asInstanceOf[InferenceRule[RuleArg]],
            new SubDiagramIndexArg(subGoalIndex, diagram.getOccurrenceIndex),name, result)
      }
    }
    catch {
      case e: TacticApplicationException => None
      case e: TransformationException => None
    }
  }


}


