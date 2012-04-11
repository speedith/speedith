package diabelli.isabelle.pure.lib
import scala.util.matching.Regex
import isabelle.Term_XML
import java.util.ArrayList

/**
 * This object provides some helper methods for converting Isabelle/Scala term
 * trees to and from the YXML format. The main purpose of these methods is to be
 * usable from Java.
 * @author Matej Urbas
 *
 */
object TermYXML {

  def main(args: Array[String]): Unit = {
    val yxml = "blabla\u00C0\u0085sdsa\u00C0sdsa\u0086\u00C0sdsadasdsa\u00C0\u0086\u00C0";
    println(yxml)
    println(unescapeControlChars(yxml))
  }
  
  /**
   * Removes the escaped control characters from the YXML string. The only escaped
   * control characters are currently "\u0005" and "\u0006", which map to
   * "\u00C0\u0085" and "\u00C0\u0086" respectively.
   */
  def unescapeControlChars(yxml: CharSequence): String = {
    if (yxml == null)
      throw new IllegalArgumentException("The YXML string must be non-null.")
    else
      (new Regex("\u00C0[\u0085\u0086]")).replaceAllIn(yxml, m => { String.valueOf((m.matched.charAt(1) - 128).asInstanceOf[Char]); })
  }
  
  /**
   * Escapes control characters in the given YXML string. The only characters
   * currently escaped are "\u0005" and "\u0006", which map to
   * "\u00C0\u0085" and "\u00C0\u0086" respectively.
   */
  def escapeControlChars(yxml: CharSequence): String = {
    if (yxml == null)
      throw new IllegalArgumentException("The YXML string must be non-null.")
    else
      (new Regex("[\u0005\u0006]")).replaceAllIn(yxml, m => { val c = (m.matched.charAt(1) + 128).asInstanceOf[Char]; String.valueOf('\u00C0', c) })
  }
  
  /**
   * Parses the given (unescaped) YXML string and returns the corresponding term. 
   */
  def parseYXML(yxml: CharSequence): isabelle.Term.Term = {
    val t: isabelle.XML.Tree = isabelle.YXML.parse(yxml)
    isabelle.Term_XML.Decode.term(List(t))
  }
  
  /**
   * Converts the given term into a YXML string (unescaped).
   */
  def outputYXML(term: isabelle.Term.Term): CharSequence = {
    val enc = isabelle.Term_XML.Encode.term(term)
    isabelle.YXML.string_of_body(enc)
  }

}