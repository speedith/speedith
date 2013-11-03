package speedith.core.reasoning.util

import speedith.core.lang.PrimarySpiderDiagram
import scala.collection.JavaConversions._

class PrimaryDiagramZoneTransfer(sourceDiagram: PrimarySpiderDiagram, destinationDiagram: PrimarySpiderDiagram) {
  // TODO: implement some algorithms for transferring zones between two diagrams.
  def missingContoursInTarget(): java.util.Set[String] = {
    sourceDiagram.getAllContours.diff(destinationDiagram.getAllContours)
  }
}
