package speedith.core.reasoning.rules.util

import java.util

import speedith.core.lang.util.HabitatUtils
import speedith.core.lang.{PrimarySpiderDiagram, Region, SpiderDiagrams, Zone}

import scala.collection.JavaConversions._

object CombiningUtils {

  def combine(leftConjunct: PrimarySpiderDiagram, rightConjunct: PrimarySpiderDiagram): PrimarySpiderDiagram = {
    val leftZonesWithSpiders = HabitatUtils.zonesToSpiders(leftConjunct)
    val rightZonesWithSpiders = HabitatUtils.zonesToSpiders(rightConjunct)
    val leftDiagramHabitats = habitatsNotInOther(leftZonesWithSpiders, rightZonesWithSpiders, leftConjunct.getHabitats)
    val rightDiagramHabitats = habitatsNotInOther(rightZonesWithSpiders, leftZonesWithSpiders, rightConjunct.getHabitats)
    val sharedHabitats = habitatsFromDiagramWithMoreSpiders(leftZonesWithSpiders, leftConjunct.getHabitats, rightZonesWithSpiders, rightConjunct.getHabitats)
    SpiderDiagrams.createPrimarySD(
      leftDiagramHabitats ++ rightDiagramHabitats ++ sharedHabitats,
      leftConjunct.getShadedZones ++ rightConjunct.getShadedZones,
      leftConjunct.getPresentZones ++ rightConjunct.getPresentZones
    )
  }

  private def habitatsNotInOther(zonesWithSpiders: Map[Zone, List[String]], otherZonesWithSpiders: Map[Zone, List[String]], habitats: util.SortedMap[String, Region]): Map[String, Region] = {
    (zonesWithSpiders.keySet -- otherZonesWithSpiders.keySet).toIterable.flatMap(zone => zonesWithSpiders(zone).map(spider => (spider, habitats(spider)))).toMap
  }

  private def habitatsFromDiagramWithMoreSpiders(leftZonesWithSpiders: Map[Zone, List[String]],
                                                 leftHabitats: util.SortedMap[String, Region],
                                                 rightZonesWithSpiders: Map[Zone, List[String]],
                                                 rightHabitats: util.SortedMap[String, Region]): Map[String, Region] = {
    val sharedHabitats = leftZonesWithSpiders.keySet.intersect(rightZonesWithSpiders.keySet)
    sharedHabitats.toIterable.flatMap {
      zone =>
        val spidersInLeft = leftZonesWithSpiders(zone)
        val spidersInRight = rightZonesWithSpiders(zone)
        if (spidersInRight.size > spidersInLeft.size) {
          spidersInRight.map(spider => (spider, rightHabitats.get(spider)))
        } else {
          spidersInLeft.map(spider => (spider, leftHabitats.get(spider)))
        }
    }.toMap
  }
}
