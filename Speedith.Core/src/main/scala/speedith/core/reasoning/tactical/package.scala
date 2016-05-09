package speedith.core.reasoning

import speedith.core.reasoning.automatic.wrappers.SpiderDiagramOccurrence

/**
 * Type definitions for tactic/tactical support.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
package object tactical {
  type Tactic = String => Goals => Int => TacticApplicationResult => Option[TacticApplicationResult]
  type Chooser[A] = SpiderDiagramOccurrence => Option[A]
  type DiagramPredicate = SpiderDiagramOccurrence => Boolean
  type GoalPredicate = Goals => Int => Boolean



}
