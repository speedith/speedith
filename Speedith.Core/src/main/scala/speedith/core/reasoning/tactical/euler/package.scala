package speedith.core.reasoning.tactical

import speedith.core.reasoning.Proof

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 *
 */
package object euler {
  type Tactical = Proof => Seq[Proof]
}
