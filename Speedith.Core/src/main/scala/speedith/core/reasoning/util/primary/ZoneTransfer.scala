package speedith.core.reasoning.util.primary

import speedith.core.lang.PrimarySpiderDiagram
import scala.collection.JavaConversions._

class ZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {

  def contoursOnlyInSource(): java.util.Set[String] = {
    sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  }

}
