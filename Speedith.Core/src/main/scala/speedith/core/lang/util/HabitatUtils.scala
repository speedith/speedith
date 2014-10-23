package speedith.core.lang.util

import speedith.core.lang.PrimarySpiderDiagram

import scala.collection.JavaConversions.asScalaSet

object HabitatUtils {

  def habitatsAreSingleZoned(diagram: PrimarySpiderDiagram): Boolean = {
    diagram.getSpiders.forall {
      spider =>
        println("Spider! " + spider)
        println("Habitat! " + diagram.getSpiderHabitat(spider))
        diagram.getSpiderHabitat(spider).getZonesCount == 1
    }
  }


}
