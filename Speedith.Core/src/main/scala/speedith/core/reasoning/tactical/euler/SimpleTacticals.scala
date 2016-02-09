package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.Proof
import speedith.core.reasoning.tactical.euler.Auxilliary._
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
      introduceShadedZone(0,isPrimaryAndContainsMissingZones,_)))(state)
  }

  def deVennify (state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),removeShadedZone(0,_)))(state)
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
    THEN(REPEAT(ORELSE(trivialTautology(0,_),
      eraseContour(0, containsOtherContours(_, concContours ), firstOfTheOtherContours(_, concContours),_))),REPEAT(ORELSE(trivialTautology(0,_), removeShadedZone(0,_))) )(state)
  }

  def copyTopologicalInformation(state : Proof) = {
    THEN(REPEAT(ORELSE(trivialTautology(0,_), removeShadedZone(0,_))) , REPEAT(ORELSE(trivialTautology(0,_), copyContour(0,_))))(state)
  }

  def copyShadings(state:Proof) = {
    REPEAT(ORELSE(trivialTautology(0,_),
      THEN(TRY(introduceShadedZone(0,sd => collectDiagramsWithMissingZonesThatCouldBeCopied(0,_).contains(sd), _)),
        copyShading(0,_))))(state)
  }
}
