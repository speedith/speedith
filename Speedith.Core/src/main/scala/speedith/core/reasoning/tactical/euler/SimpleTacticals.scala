package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
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

  def vennify(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      introduceShadedZone(0,isPrimaryAndContainsMissingZones,anyMissingZone,_)))(state)
  }

  def deVennify (state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),removeShadedZone(0,anyShadedZone,_)))(state)
  }


  def unifyContourSets(state:Proof) = {
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram(0),  ORELSE(trivialTautology(0,_),introduceContour(0,_)))(state)
  }

  def eraseAllContours(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      eraseContour(0,containsContours, anyContour,_)))(state)
  }

  def combineAll(state : Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      combine(0,_)))(state)
  }

  def vennStyle(state : Proof) = {
    THEN(unifyContourSets, THEN(vennify, THEN(combineAll, matchConclusion)))(state)
  }

  def matchConclusion(state : Proof) = {
    val concContours =getContoursInConclusion(0,state)
    val concShadedZones = getShadedZonesInConclusion(0,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(0,state)
    THEN(
      THEN(
        THEN(
          REPEAT(ORELSE(trivialTautology(0,_),
            eraseContour(0, containsOtherContours(concContours ), firstOfTheOtherContours(concContours),_))),
          REPEAT(ORELSE(trivialTautology(0,_) ,
            eraseShading(0,isPrimaryAndContainsShadedZones, someVisibleShadedZonesInGivenZones(concUnshadedZones),_)))),
      REPEAT(ORELSE(trivialTautology(0,_), removeShadedZone(0,firstVisibleShadedZoneNotInGivenZones(concShadedZones),_)))),
      REPEAT(ORELSE(trivialTautology(0,_),
        introduceShadedZone(0,isPrimaryAndContainsMissingZones, firstMissingZoneInGivenZones(concShadedZones),_))))(state)
  }

  def copyTopologicalInformation(state : Proof) = {
      REPEAT(ORELSE(trivialTautology(0,_),
        ORELSE(idempotency(0,_),
          ORELSE(removeShadedZone(0,anyShadedZone,_),
            copyContour(0,_)))))(state)
  }

  def copyShadings(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      ORELSE(idempotency(0,_),
        ORELSE(copyShading(0,_),
          introduceShadedZone(0,collectDiagramsWithMissingZonesThatCouldBeCopied(0,_).contains, anyMissingZone, _)))))(state)
  }
}
