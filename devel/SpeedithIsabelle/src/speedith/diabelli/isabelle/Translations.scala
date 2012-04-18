package speedith.diabelli.isabelle
import isabelle.Term._
import speedith.core.lang.SpiderDiagram
import speedith.core.lang.reader.ReadingException
import diabelli.isabelle.pure.lib.TermYXML._
import diabelli.isabelle.pure.lib.TermUtils._
import speedith.core.lang.Operator
import speedith.core.lang.Operator._

object Translations {

  def main(args: Array[String]): Unit = {
    var sd: SpiderDiagram = termToSpiderDiagram(parseYXML(Example5_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example4_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example3_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example2_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example1_unescapedYXML));
    println(sd);
  }
  
  def isaOperators2SDOperators(operator:String): Operator = {
    operator match {
      case HOLConjunction => Conjunction
      case HOLDisjunction => Disjunction
      case HOLImplication => Implication
      case HOLEquality => Equivalence
      case MetaImplication => Implication
      case HOLNot => Negation
      case _ => throw new ReadingException("Could not translate the formula to a spider diagram. Found an unknown operator: " + operator)
    }
  }

  /**
   * Takes an Isabelle term and tries to translate it to a spider diagram.
   */
  @throws(classOf[ReadingException])
  def termToSpiderDiagram(t: Term): SpiderDiagram = {
    println(t);
    t match {
      case App(App(Const(operator, typ), lhs), rhs) => {
        // We've got a binary operator. Create a compound spider diagram out of
        // it:
        //binary2csd(isaOperators2SDOperators(operator), typ, lhs, rhs);
        println("Found an operator: " + t.toString());
      }
      case App(Const(HOLNot, typ), operand) => {
        // We've got the negation.
        //unary2csd(Negation, operand);
        println("Found a negation: " + t.toString());
      }
      case App(Const(HOLExistential, typ), Abs(spider, spiderTyp, body)) => {
        println("Found an existential quantifier: " + t.toString());
      }
      case App(Const(HOLTrueprop, typ), body) => {
        println("Found an HOL goal: " + t.toString());
      }
      case App(Const(MetaAll, typ), Abs(spider, spiderTyp, body)) => {
        println("Found a global universal meta-quantification: " + t.toString());
      }
      case _ => throw new ReadingException("Could not translate the formula to a spider diagram. Found an unknown term: " + t.toString());
    }
    return null;
  }

}