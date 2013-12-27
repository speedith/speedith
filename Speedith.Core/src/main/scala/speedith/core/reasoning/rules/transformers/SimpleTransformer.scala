package speedith.core.reasoning.rules.transformers

import speedith.core.lang._
import scala.collection.JavaConversions
import scala.collection.mutable

abstract class SimpleTransformer extends Transformer {

  protected var _isDone: Boolean = false

  protected def transform(spiderDiagram: SpiderDiagram, currentDiagramIndex: Int, parents: mutable.Buffer[CompoundSpiderDiagram], childIndices: mutable.Buffer[Int]): SpiderDiagram

  override def transform(sd: PrimarySpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    transform(sd, diagramIndex, JavaConversions.asScalaBuffer(parents), JavaConversions.asScalaBuffer(childIndices).asInstanceOf[mutable.Buffer[Int]])
  }

  override def transform(sd: NullSpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    transform(sd, diagramIndex, JavaConversions.asScalaBuffer(parents), JavaConversions.asScalaBuffer(childIndices).asInstanceOf[mutable.Buffer[Int]])
  }


  override def transform(sd: CompoundSpiderDiagram, diagramIndex: Int, parents: java.util.ArrayList[CompoundSpiderDiagram], childIndices: java.util.ArrayList[java.lang.Integer]): SpiderDiagram = {
    transform(sd, diagramIndex, JavaConversions.asScalaBuffer(parents), JavaConversions.asScalaBuffer(childIndices).asInstanceOf[mutable.Buffer[Int]])
  }


  override def isDone: Boolean = {
    _isDone
  }
}
