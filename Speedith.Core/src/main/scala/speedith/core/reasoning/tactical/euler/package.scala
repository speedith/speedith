package speedith.core.reasoning.tactical

import speedith.core.reasoning.Proof

/**
 * Type definitions for tactic/tactical support.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
package object euler {
  type Tactical = Proof => Option[Proof]
}
