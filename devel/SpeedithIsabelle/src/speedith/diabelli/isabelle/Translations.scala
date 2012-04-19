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

  def isaOperators2SDOperators(operator: String): Operator = {
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
    val (sd, spiderType) = recognise(t, null);
    return sd;
  }

  private type In = ( /*term:*/ Term, /*spiderType:*/ Typ);
  private type Out = (SpiderDiagram, /*spiderType:*/ Typ);
  private type Convertor = PartialFunction[In, Out];

  private val recognise: Convertor = {
    case x => (recogniseBinaryHOLOperator
      orElse recogniseMetaAll
      orElse recogniseMetaImplication
      orElse recogniseTrueprop
      orElse recogniseExistential
      orElse recogniseNegation)(x)
  }

  private val recogniseBinaryHOLOperator: Convertor = {
    case (App(App(Const(operator, typ), lhs), rhs), spiderType) if HOLBinaryOperators contains operator => {
      // We've got a binary HOL operator
      println("Binary HOL operator: " + operator);
      val (sd, newSpiderType) = recognise(lhs, spiderType);
      recognise(rhs, newSpiderType);
    }
  };

  private val recogniseNegation: Convertor = {
    case (App(Const(HOLNot, typ), body), spiderType) => {
      // We've got a binary HOL operator
      println("Got negation!");
      recognise(body, spiderType);
    }
  };

  private val recogniseMetaImplication: Convertor = {
    case (App(App(Const(MetaImplication, typ), lhs), rhs), spiderType) => {
      // We've got a binary HOL operator
      println("Got meta implication!");
      recognise(lhs, spiderType);
      recognise(rhs, spiderType);
    }
  };

  private val recogniseExistential: Convertor = {
    case (App(Const(HOLExistential, typ), Abs(spider, spiderTyp, body)), spiderType) => {
      // We've got a binary HOL operator
      println("Got existential!");
      (null, typ);
    }
  };
  
  private val recogniseTrueprop: Convertor = {
    case (App(Const(HOLTrueprop, typ), body), spiderType) => recognise (body, spiderType)
  }
  
  private val recogniseMetaAll: Convertor = {
    case (App(Const(MetaAll, typ), Abs(spider, newSpiderType, body)), spiderType) => {
      println("Got meta existential!");
      // Collect all quantified spiders and try to convert the premises into a
      // single spider diagram
      
      // Tactic:
      // 	- fetch all premises that in any way mention the quantified spiders.
      (null, typ);
    }
  }

}