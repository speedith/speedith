package speedith.core.lang.util

import scala.collection.JavaConversions

object SpiderUtils {

  val NUMBERED_SPIDER_PATTERN = "(\\w*0*)(\\d+)(\\w*)".r

  def freshSpiderName(allSpiders: java.util.Set[String]): String = {
    freshSpiderName(JavaConversions.asScalaSet(allSpiders))
  }

  def freshSpiderName(allSpiders: collection.Set[String]): String = {
    allSpiders.headOption match {
      case None =>
        "s"
      case Some(spiderName) =>
        spiderName match {
          case NUMBERED_SPIDER_PATTERN(prefix, number, suffix) =>
            freshSpiderName(allSpiders, number.toInt, prefix, suffix)
          case _ =>
            freshSpiderName(allSpiders, 1, spiderName, "")
        }
    }
  }

  private def freshSpiderName(allSpiders: collection.Set[String], searchStartNumber: Int, prefix: String, suffix: String): String = {
    searchStartNumber.to(2000000000).view
      .map(number => prefix + number + suffix)
      .find(newSpiderName => !allSpiders.contains(newSpiderName))
      .getOrElse(throw new UnsupportedOperationException("Could not find a fresh name amongst " + allSpiders.mkString(", ")))
  }
}
