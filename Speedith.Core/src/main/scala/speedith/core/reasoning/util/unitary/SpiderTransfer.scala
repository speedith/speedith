package speedith.core.reasoning.util.unitary

import speedith.core.lang.PrimarySpiderDiagram
import speedith.core.lang.SpiderDiagrams.createPrimarySD

class SpiderTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {
  def transferSpider(spider: String): PrimarySpiderDiagram = {
    if (!sourceDiagram.containsSpider(spider)) {
      throw new IllegalArgumentException("The spider '" + spider + "' is not in the source diagram.")
    }
    sourceDiagram
  }
}
