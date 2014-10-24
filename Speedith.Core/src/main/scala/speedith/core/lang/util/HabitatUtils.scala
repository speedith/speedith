package speedith.core.lang.util

import speedith.core.lang.PrimarySpiderDiagram

import scala.collection.JavaConversions._

object HabitatUtils {

  def habitatsAreSingleZoned(diagram: PrimarySpiderDiagram): Boolean = {
    diagram.getHabitats.values.forall(_.getZonesCount == 1)
  }


}
