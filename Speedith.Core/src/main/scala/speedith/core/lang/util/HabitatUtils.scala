package speedith.core.lang.util

import speedith.core.lang.{PrimarySpiderDiagram, Zone}

import scala.collection.JavaConversions._

object HabitatUtils {


  def habitatsAreSingleZoned(diagram: PrimarySpiderDiagram): Boolean = {
    diagram.getHabitats.values.forall(_.getZonesCount == 1)
  }

  def zonesToSpiders(diagram: PrimarySpiderDiagram): Map[Zone, List[String]] = {
    var zonesToSpidersMap = Map.empty[Zone, List[String]].withDefaultValue(List.empty[String])
    diagram.getHabitats.foreach {
      case (spider, habitat) =>
        habitat.zones.foreach {
          zone =>
            zonesToSpidersMap += (zone -> (spider :: zonesToSpidersMap(zone)))
        }
    }
    zonesToSpidersMap
  }


}
