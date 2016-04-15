package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.tactical.TacticApplicationResult
import speedith.core.reasoning.{Goals, Proof}
import speedith.core.reasoning.rules.util.AutomaticUtils
import speedith.core.reasoning.tactical.euler.Auxilliary._
import speedith.core.reasoning.tactical.euler.Choosers._
import speedith.core.reasoning.tactical.euler.Predicates._
import speedith.core.reasoning.tactical.euler.BasicTacticals._
import speedith.core.reasoning.tactical.euler.Tactics._

/**
 * Basic tacticals to work on a proof. The tacticals chain several tactics
  * by using the [[BasicTacticals basic tacticals]].
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
object SimpleTacticals {

  def vennify : Tactical = {
    REPEAT(ORELSE(trivialTautology,
      introduceShadedZone(isPrimaryAndContainsMissingZones,someMissingZone)))
  }

  def vennifyFast : Tactical = {
    REPEAT(ORELSE(trivialTautology,
      introduceShadedZone(isPrimaryAndContainsMissingZones,allMissingZones)))
  }

  def deVennify : Tactical = {
    REPEAT(ORELSE(trivialTautology,removeShadedZone(someShadedZone)))
  }

  def deVennifyFast : Tactical = {
    REPEAT(ORELSE(trivialTautology,removeShadedZone(allShadedZones)))
  }


  def unifyContourSets : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) =>{
    val contours = getContoursInSubGoal(subGoalIndex, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(subGoalIndex),
      ORELSE(trivialTautology,introduceContour( containsLessContours(contours), someGivenContoursButNotInDiagram(contours))))(name)(state)(subGoalIndex)(result)
  }

  def unifyContourSetsFast : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) =>{
    val contours = getContoursInSubGoal(subGoalIndex, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(subGoalIndex),
      ORELSE(trivialTautology,introduceContour(containsLessContours(contours), allInGivenContoursButNotInDiagram(contours))))(name)(state)(subGoalIndex)(result)
  }
/*
  def eraseAllContours : Tactical = {
    REPEAT(ORELSE(trivialTautology(0),
      eraseContour(0,containsContours, anyContour)))
  }
*/
  def combineAll : Tactical = {
    REPEAT(ORELSE(trivialTautology,
      combine))
  }

  def vennStyle : Tactical = {
    THEN(vennify, THEN(unifyContourSets, THEN(combineAll, matchConclusion)))
  }

  def vennStyleFast : Tactical = {
    THEN(unifyContourSetsFast, THEN(vennifyFast, THEN(combineAll, matchConclusionFast)))
  }


  def matchConclusionFast : Tactical = (name:String) => (state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) =>{
    val concContours =getContoursInConclusion(subGoalIndex,state)
    val concShadedZones = getShadedZonesInConclusion(subGoalIndex,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(subGoalIndex,state)
    val concVisibleZones = getVisibleZonesInConclusion(subGoalIndex,state)
    THEN(
      THEN(
        THEN(
          REPEAT(ORELSE(trivialTautology,
            eraseContour(containsOtherContours(concContours), allInDiagramButNotInGivenContours(concContours)))),
          REPEAT(ORELSE(trivialTautology,
            introduceShadedZone(isPrimaryAndContainsMissingZones, allMissingZonesInGivenZones(concVisibleZones))))),
        REPEAT(ORELSE(trivialTautology ,
          eraseShading(isPrimaryAndContainsShadedZones, allVisibleShadedZonesInGivenZones(concUnshadedZones))))),
        REPEAT(ORELSE(trivialTautology,
          removeShadedZone(allVisibleShadedZoneNotInGivenZones(concShadedZones)))))(name)(state)(subGoalIndex)(result)
  }

  def matchConclusion : Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    val concContours =getContoursInConclusion(subGoalIndex,state)
    val concShadedZones = getShadedZonesInConclusion(subGoalIndex,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(subGoalIndex,state)
    val concVisibleZones = getVisibleZonesInConclusion(subGoalIndex,state)
    THEN(
      THEN(
        THEN(
          REPEAT(ORELSE(trivialTautology,
            eraseContour(containsOtherContours(concContours ), someInDiagramButNotInGivenContours(concContours)))),
          REPEAT(ORELSE(trivialTautology,
            introduceShadedZone(isPrimaryAndContainsMissingZones, someMissingZoneInGivenZones(concVisibleZones))))),
          REPEAT(ORELSE(trivialTautology,
            eraseShading(isPrimaryAndContainsShadedZones, someVisibleShadedZonesInGivenZones(concUnshadedZones))))),
          REPEAT(ORELSE(trivialTautology,
            removeShadedZone(someVisibleShadedZoneNotInGivenZones(concShadedZones)))))(name)(state)(subGoalIndex)(result)
  }


  def copyTopologicalInformation : Tactical =  (name:String) => (state:Goals) => (subGoalIndex: Int) => (result:TacticApplicationResult) => {
      REPEAT(ORELSE(trivialTautology,
        ORELSE(idempotency,
          ORELSE(removeShadedZone(someShadedZone),
            copyContour))))(name)(state)(subGoalIndex)(result)
  }

  def copyShadings: Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) =>{
    REPEAT(ORELSE(trivialTautology,
      ORELSE(idempotency,
        ORELSE(copyShading,
          introduceShadedZone(collectDiagramsWithMissingZonesThatCouldBeCopied(subGoalIndex,_).contains, someMissingZone)))))(name)(state)(subGoalIndex)(result)
  }

  def copyEveryThing: Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
    THEN(DEPTH_FIRST(isSingleUnitaryDiagram(subGoalIndex),
      THEN(DEPTH_FIRST(containsNoDiagramsWithShadedZonesThatCouldBeCopied( subGoalIndex), copyShadings),
        copyTopologicalInformation)),
      matchConclusion)(name)(state)(subGoalIndex)(result)
  }
}
