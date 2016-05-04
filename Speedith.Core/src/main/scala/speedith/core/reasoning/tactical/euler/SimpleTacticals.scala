package speedith.core.reasoning.tactical.euler

import speedith.core.reasoning.automatic.wrappers.CompoundSpiderDiagramOccurrence
import speedith.core.reasoning.tactical.TacticApplicationResult
import speedith.core.reasoning.Goals
import speedith.core.reasoning.rules.util.ReasoningUtils
import speedith.core.reasoning.tactical.euler.Auxilliary._
import speedith.core.reasoning.tactical.euler.Choosers._
import speedith.core.reasoning.tactical.euler.Predicates._
import speedith.core.reasoning.tactical.euler.BasicTacticals._
import speedith.core.reasoning.tactical.euler.Tactics._

  /**
  * Tactics to work on a proof. The Tactics chain several tactics
  * by using the [[BasicTacticals basic tacticals]]. Some of these
  * tactics are normally able to remove a subgoal, as long as it consists
  * of an implication, where the conclusion is a single unitary diagram (and if the
  * conclusion is a consequence of the premises)
   *
  * @author Sven Linker [s.linker@brighton.ac.uk]
  *
  */
object SimpleTacticals {

  def vennify : Tactical = {
    REPEAT(
      ORELSE(trivialTautology)(
      introduceShadedZone(isPrimaryAndContainsMissingZones,someMissingZone)))
  }

  def vennifyFast : Tactical = {
    REPEAT(ORELSE(trivialTautology)(
      introduceShadedZone(isPrimaryAndContainsMissingZones,allMissingZones)))
  }

  def deVennify : Tactical = {
    REPEAT(ORELSE(trivialTautology)(removeShadedZone(someShadedZone)))
  }

  def deVennifyFast : Tactical = {
    REPEAT(ORELSE(trivialTautology)(removeShadedZone(allShadedZones)))
  }


  def unifyContourSets : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) =>{
    val contours = getContoursInSubGoal(subGoalIndex, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram)(
      ORELSE(trivialTautology)(introduceContour( containsLessContours(contours), someGivenContoursButNotInDiagram(contours))))(name)(state)(subGoalIndex)(result)
  }

  def unifyContourSetsFast : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) =>{
    val contours = getContoursInSubGoal(subGoalIndex, state)
    DEPTH_FIRST(equalContourSetsInEachPrimaryDiagram)(
      ORELSE(trivialTautology)(introduceContour(containsLessContours(contours), allInGivenContoursButNotInDiagram(contours))))(name)(state)(subGoalIndex)(result)
  }

  def combineAll : Tactical = {
    REPEAT(ORELSE(trivialTautology)(
      combine))
  }

  def vennStyle : Tactical = {
    THEN(vennify)(THEN(unifyContourSets)(THEN(combineAll)(matchConclusion)))
  }

  def vennStyleFast : Tactical = {
    THEN(unifyContourSetsFast)(THEN(vennifyFast)(THEN(combineAll)(matchConclusionFast)))
  }


  def vennifyFocused : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) => {
    val target = getDeepestNestedDiagram(subGoalIndex)(state)
    target match {
      case None => id(name)(state)(subGoalIndex)(result)
      case Some(diagram) => REPEAT(ORELSE(trivialTautology)( introduceShadedZone( AND(isOperand(diagram), isPrimaryAndContainsMissingZones), someMissingZone)))(name)(state)(subGoalIndex)(result)
    }
  }

  def unifyContourSetsFocused : Tactical = (name:String) => (state:Goals) => (subGoalIndex : Int) => (result : TacticApplicationResult) => {
    val target = getDeepestNestedDiagram(subGoalIndex)(state)
    target match {
      case None => id(name)(state)(subGoalIndex)(result)
      case Some(diagram) =>
        val contours = collectContours(diagram)
        REPEAT(
          ORELSE(
            trivialTautology)(
            introduceContour(
              AND(isOperand(diagram), containsLessContours(contours)),
              someGivenContoursButNotInDiagram(contours)
            )
          )
        )(name)(state)(subGoalIndex)(result)
    }
  }

    /**
      * Chooses one conjunction of primary diagrams, changes both conjuncts into Venn diagrams and unifies their
      * contour sets. Afterwards combines the diagrams. Repeats this procedure as long as only a unitary
      * diagram is left.
      * @return
      */
  def vennStyleFocused : Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
      THEN(
        DEPTH_FIRST(isUnitaryDiagram)(
          THEN(
            THEN(
              vennifyFocused)(
              unifyContourSetsFocused))(
            combineAll)))(
        matchConclusion)(name)(state)(subGoalIndex)(result)

  }


  def matchConclusionFast : Tactical = (name:String) => (state: Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) =>{
    val concContours =getContoursInConclusion(subGoalIndex,state)
    val concShadedZones = getShadedZonesInConclusion(subGoalIndex,state)
    val concUnshadedZones = getUnshadedZonesInConclusion(subGoalIndex,state)
    val concVisibleZones = getVisibleZonesInConclusion(subGoalIndex,state)
    THEN(
      THEN(
        THEN(
          THEN(
            REPEAT(ORELSE(trivialTautology)(
              introduceContour(containsLessContours(concContours), someGivenContoursButNotInDiagram(concContours)))))(
            REPEAT(ORELSE(trivialTautology)(
              eraseContour(containsOtherContours(concContours), allInDiagramButNotInGivenContours(concContours))))))(
          REPEAT(ORELSE(trivialTautology)(
            introduceShadedZone(isPrimaryAndContainsMissingZones, allMissingZonesInGivenZones(concVisibleZones))))))(
        REPEAT(ORELSE(trivialTautology)(
          eraseShading(isPrimaryAndContainsShadedZones, allVisibleShadedZonesInGivenZones(concUnshadedZones))))))(
      REPEAT(ORELSE(trivialTautology)(
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
          THEN(
            REPEAT(ORELSE(trivialTautology)(
              introduceContour(containsLessContours(concContours), someGivenContoursButNotInDiagram(concContours)))))(
            REPEAT(ORELSE(trivialTautology)(
              eraseContour(containsOtherContours(concContours), someInDiagramButNotInGivenContours(concContours))))))(
          REPEAT(ORELSE(trivialTautology)(
            introduceShadedZone(isPrimaryAndContainsMissingZones, someMissingZoneInGivenZones(concVisibleZones))))))(
        REPEAT(ORELSE(trivialTautology)(
          eraseShading(isPrimaryAndContainsShadedZones, someVisibleShadedZonesInGivenZones(concUnshadedZones))))))(
      REPEAT(ORELSE(trivialTautology)(
        removeShadedZone(someVisibleShadedZoneNotInGivenZones(concShadedZones)))))(name)(state)(subGoalIndex)(result)
  }


    /**
      * Applies Copy Contour as often as possible. Also uses Remove Shaded Zone to increase the semantic information that
      * is copied. (If a zone is visible and shaded, this shading information is not taken into account by Copy Contour.
      * If the zone is missing however, its information is used in the copy procedure)
     *
      * @return
      */
  def copyTopologicalInformation : Tactical =  (name:String) => (state:Goals) => (subGoalIndex: Int) => (result:TacticApplicationResult) => {
      REPEAT(
        ORELSE(
          trivialTautology)(
          ORELSE(
            idempotency)(
            ORELSE(
              removeShadedZone(someShadedZone)
            )(
              copyContour)
          )
        )
      )(name)(state)(subGoalIndex)(result)
  }

    /**
      * Tries to apply Copy Shading to the goal as often as possible (while copying maximal shaded regions). If
      * no shaded zones that can be copied exist, it tries to introduce shaded zones to create new possibilities to
      * copy shadings.
      *
      * @return
      */
  def copyShadings: Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) =>{
      REPEAT(
        ORELSE(
          trivialTautology)(
          ORELSE(
            idempotency)(
            ORELSE(
              copyShading)(
              introduceMissingZonesToCopy
            )
          )
        )
      )(name)(state)(subGoalIndex)(result)
  }

  def copyEveryThing: Tactical =  { //(name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) => {
     THEN(
       DEPTH_FIRST(isUnitaryDiagram)(
          THEN(
            DEPTH_FIRST(containsNoDiagramsWithShadedZonesThatCouldBeCopied)( copyShadings)
          )(
            COND(isUnitaryDiagram)(id)(copyTopologicalInformation)
          )
        )
     )(matchConclusion)
     //(name)(state)(subGoalIndex)(result)
  }

    /**
      * Applies Introduce Shaded Zone to create new possibilites to for Copy Shading to be applied.
      * @return
      */
  def introduceMissingZonesToCopy : Tactical = (name:String) => (state:Goals) => (subGoalIndex:Int) => (result:TacticApplicationResult) =>{
    val goal = getSubGoal(subGoalIndex,state)
    if (ReasoningUtils.isImplicationOfConjunctions(goal)) {
      val target = firstMatchingDiagram(goal.asInstanceOf[CompoundSpiderDiagramOccurrence].getOperand(0), isConjunctionContainingMissingZonesToCopy).asInstanceOf[Option[CompoundSpiderDiagramOccurrence]]
      target match {
        case None => fail(name)(state)(subGoalIndex)(result)
        case Some(d) => introduceShadedZone(AND(isOperand(d), isPrimaryAndContainsMissingZones), allMissingZonesContainingOneContour)(name)(state)(subGoalIndex)(result)
      }
    } else { fail(name)(state)(subGoalIndex)(result) }
  }
}