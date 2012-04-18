package speedith.diabelli.isabelle
import isabelle.Term
import speedith.core.lang.SpiderDiagram
import speedith.core.lang.reader.ReadingException
import diabelli.isabelle.pure.lib.TermYXML

object Translations {

  def main(args: Array[String]): Unit = {
    var sd: SpiderDiagram = fromTermToSpiderDiagram(TermYXML.parseYXML(TermYXML.Example5_unescapedYXML));
    sd = fromTermToSpiderDiagram(TermYXML.parseYXML(TermYXML.Example4_unescapedYXML));
    println(sd);
  }

  /**
   * Takes an Isabelle term and tries to translate it to a spider diagram.
   */
  @throws(classOf[ReadingException])
  def fromTermToSpiderDiagram(t: Term.Term): SpiderDiagram = {
    t match {
      case _ =>
    }
    return null;
  }

}