package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
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
    REPEAT(ORELSE(trivialTautology(0),
      introduceShadedZone(0,isPrimaryAndContainsMissingZones,anyMissingZone)))
  }

  def deVennify : Tactical = {
    REPEAT(ORELSE(trivialTautology(0),removeShadedZone(0,anyShadedZone)))
  }

  def deVennifyFast : Tactical = {
    REPEAT(ORELSE(trivialTautology(0),removeShadedZone(0,allShadedZones)))
  }


  def unifyContourSets : Tactical = (name:String) => (state:Proof) => {
    val contours = getContoursInSubGoal(0, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(0),
      ORELSE(trivialTautology(0),introduceContour(0, containsLessContours(contours), someGivenContoursButNotInDiagram(contours))))(name)(state)
  }

  def unifyContourSetsFast : Tactical = (name:String) => (state:Proof) => {
    val contours = getContoursInSubGoal(0, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(0),
      ORELSE(trivialTautology(0),introduceContour(0, containsLessContours(contours), allInGivenContoursButNotInDiagram(contours))))(name)(state)
  }

  def eraseAllContours : Tactical = {
    REPEAT(ORELSE(trivialTautology(0),
      eraseContour(0,containsContours, anyContour)))
  }

  def combineAll : Tactical = {
    REPEAT(ORELSE(trivialTautology(0),
      combine(0)))
  }

  def vennStyle : Tactical = {
    THEN(unifyContourSets, THEN(vennify, THEN(combineAll, matchConclusion)))
  }

  def vennStyleFast : Tactical = {
    THEN(unifyContourSetsFast, THEN(vennify, THEN(combineAll, matchConclusionFast)))
  }

  def matchConclusionFast : Tactical = (name:String) => (state: Proof) => {
    val concContours =getContoursInConclusion(0,state)
    val concShadedZones = getShadedZonesInConclusion(0,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(0,state)
    val concVisibleZones = getVisibleZonesInConclusion(0,state)
    THEN(
      THEN(
        THEN(
          REPEAT(ORELSE(trivialTautology(0),
            eraseContour(0, containsOtherContours(concContours ), allInDiagramButNotInGivenContours(concContours)))),
          REPEAT(ORELSE(trivialTautology(0),
            introduceShadedZone(0,isPrimaryAndContainsMissingZones, someMissingZoneInGivenZones(concVisibleZones))))),
        REPEAT(ORELSE(trivialTautology(0) ,
          eraseShading(0,isPrimaryAndContainsShadedZones, allVisibleShadedZonesInGivenZones(concUnshadedZones))))),
      REPEAT(ORELSE(trivialTautology(0), removeShadedZone(0,allVisibleShadedZoneNotInGivenZones(concShadedZones)))))(name)(state)
  }

  def matchConclusion : Tactical = (name:String) => (state:Proof) => {
    val concContours =getContoursInConclusion(0,state)
    val concShadedZones = getShadedZonesInConclusion(0,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(0,state)
    val concVisibleZones = getVisibleZonesInConclusion(0,state)
    THEN(
      THEN(
        THEN(
          REPEAT(ORELSE(trivialTautology(0),
            eraseContour(0, containsOtherContours(concContours ), someInDiagramButNotInGivenContours(concContours)))),
          REPEAT(ORELSE(trivialTautology(0),
            introduceShadedZone(0,isPrimaryAndContainsMissingZones, someMissingZoneInGivenZones(concVisibleZones))))),
          REPEAT(ORELSE(trivialTautology(0) ,
            eraseShading(0,isPrimaryAndContainsShadedZones, someVisibleShadedZonesInGivenZones(concUnshadedZones))))),
      REPEAT(ORELSE(trivialTautology(0), removeShadedZone(0,someVisibleShadedZoneNotInGivenZones(concShadedZones)))))(name)(state)
  }

  def copyTopologicalInformation : Tactical = {
      REPEAT(ORELSE(trivialTautology(0),
        ORELSE(idempotency(0),
          ORELSE(removeShadedZone(0,anyShadedZone),
            copyContour(0)))))
  }

  def copyShadings: Tactical = {
    REPEAT(ORELSE(trivialTautology(0),
      ORELSE(idempotency(0),
        ORELSE(copyShading(0),
          introduceShadedZone(0,collectDiagramsWithMissingZonesThatCouldBeCopied(0,_).contains, anyMissingZone)))))
  }
}
