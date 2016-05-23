package speedith.core.reasoning

import speedith.core.lang.{PrimarySpiderDiagram, CompoundSpiderDiagram, SpiderDiagram}
import speedith.core.reasoning.rules.{CopySpider, CopyShading, CopyContoursTopological, CopyContours}
import scala.collection.JavaConversions._

/**
  * Methods to analyse a given proof.
  *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object ProofAnalyser  {

  def averageClutter(proof  : Proof) : Double = {
    proof.getGoals.filter(p => !p.isEmpty).map(clutterScore).sum.toDouble / length(proof)
  }

  def maximumClutter(proof:Proof) : Int = {
    proof.getGoals.filter(p => !p.isEmpty).map(clutterScore).max
  }

  /**
    * Computes the clutter score for the given spider diagram. For a primary spider
    * diagram, the clutter score is sum of its contour score (see TODO reference!)
    * and the number of shaded zones. The clutter score of a compound diagram is the sum
    * of the clutter score of its subdiagrams.
 *
    * @param diagram The spider diagram to compute the clutter score for
    * @return the clutter score of the given spider diagram
    */
  def clutterScore(diagram : SpiderDiagram): Int = diagram match {
    case sd : PrimarySpiderDiagram =>
      sd.getPresentZones.toList.map(_.getInContoursCount).sum + (sd.getShadedZones & sd.getPresentZones).size
    case sd:CompoundSpiderDiagram =>
      sd.getOperands.map(clutterScore).sum
  }

  /**
    * The clutter score of a single goal is the sum of the clutter score of all its subgoals.
    *
    * @param goals the set of goals to compute the clutter score for
    * @return the clutter score of the given goals
    */
  def clutterScore(goals: Goals): Int = {
    goals.getGoals.map(clutterScore).sum
  }

  def complexRuleCount(proof : Proof) : Int = {
    proof.getInferenceApplications.map(r => r.getInference match  {
      case r1 : CopyContours  => 1
      case r2 : CopyContoursTopological => 1
      case r3 : CopyShading => 1
      case r4 : CopySpider => 1
      case _ => 0
    }).sum
  }

  def averageNumberOfComplexRules(proof: Proof) : Double ={
    complexRuleCount(proof).toDouble / length(proof)
  }

  def length(proof: Proof) : Int = proof.getInferenceApplicationCount

  def numberOfInteractions(proof : Proof) : Int = {
    val interactiveApps =  proof.getInferenceApplications.count(app => app.getType.equals(RuleApplicationType.INTERACTIVE))
    val methodInvocations = numberOfProofMethodInvocations(proof.getInferenceApplications.toList)
    interactiveApps + methodInvocations
  }

  def numberOfProofMethodInvocations(apps : List[InferenceApplication]) : Int = apps match {
    case Nil => 0
    case app :: Nil => 0
    case app1 :: app2 :: x =>
     val rest = numberOfProofMethodInvocations(app2::x)
      if(!app2.getType.equals(RuleApplicationType.INTERACTIVE) &&
        (app1.getType != app2.getType || !app1.getTypeSpecifier.equals(app2.getTypeSpecifier)))
      {
        1+rest
      } else {
        0+rest
      }
  }

  def averageInteractions(proof:Proof) : Double = {
    numberOfInteractions(proof).toDouble /length(proof)
  }

  def maximalClutterVelocity(proof : Proof) : Int = {
    val goals = proof.getGoals.filter(g => !g.isEmpty).toList
    if (goals.size > 1) {
      val tuples = goals.sliding(2).map(t => t match {
        case List(x, y) => clutterScore(x) - clutterScore(y)
      })
      val list = tuples.toList.map(i => if (i < 0) -i else i)
      list.max
    } else {
      0
    }
  }

  def numberOfAutomaticRuleApplications(proof : Proof) : Int = {
    proof.getInferenceApplications.count(app => app.getType.equals(RuleApplicationType.AUTOMATIC))
  }
}
