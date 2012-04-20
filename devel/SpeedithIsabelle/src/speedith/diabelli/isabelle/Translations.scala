package speedith.diabelli.isabelle
import isabelle.Term._
import speedith.core.lang.SpiderDiagram
import speedith.core.lang.SpiderDiagrams
import speedith.core.lang.reader.ReadingException
import diabelli.isabelle.pure.lib.TermYXML._
import diabelli.isabelle.pure.lib.TermUtils._
import speedith.core.lang.Operator
import speedith.core.lang.Operator._
import scala.collection.immutable.HashMap
import java.util.ArrayList
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Buffer
import speedith.core.lang.PrimarySpiderDiagram

object Translations {

  def main(args: Array[String]): Unit = {
    var sd: SpiderDiagram = termToSpiderDiagram(parseYXML(Example6_unescapedYXML));
    println(sd);
    sd = termToSpiderDiagram(parseYXML(Example4_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example5_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example3_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example2_unescapedYXML));
    sd = termToSpiderDiagram(parseYXML(Example1_unescapedYXML));
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

  val BinaryOperators = Set(HOLConjunction, HOLDisjunction, HOLImplication, HOLEquality, MetaImplication);

  val DistinctFunction = "List.distinct";

  private def operatorsIsaToSD = HashMap(
    HOLConjunction -> Conjunction,
    HOLDisjunction -> Disjunction,
    HOLImplication -> Implication,
    HOLEquality -> Equivalence,
    MetaImplication -> Implication,
    HOLNot -> Negation);

  private def extractConjuncts(term: Term, conjuncts: Buffer[Term]): Unit = {
    term match {
      case App(App(Const(HOLConjunction, _), lhs), rhs) => {
        extractConjuncts(lhs, conjuncts);
        extractConjuncts(rhs, conjuncts);
      }
      case x => conjuncts += x;
    }
  }

  private def extractConjuncts(terms: Traversable[Term], conjuncts: Buffer[Term]): Unit = {
    terms foreach { term => extractConjuncts(term, conjuncts); }
  }

  /**
   * Extracts HOL existentially quantified variables from the term, puts them
   * into the given array list packed as separate `Free`s, and returns the
   * body.
   */
  def extractSpidersAndBody(t: Term, variables: Buffer[Free]): Term = {
    t match {
      case App(Const(HOLExistential, _), Abs(varName, varType, body)) => {
        variables += Free(varName, varType);
        extractSpidersAndBody(body, variables);
      }
      case _ => t
    }
  }

  private def checkSpiderType(newSpiderType: Typ, oldSpiderType: Typ): Boolean = {
    if (oldSpiderType == null) true else oldSpiderType.equals(newSpiderType);
  }

  private def extractDistinctTerm(conjuncts: Buffer[Term]): Term = {
    val distinctTerms = conjuncts collect { case t @ App(Const(DistinctFunction, _), _) => t };
    if (distinctTerms.length > 1) throw new ReadingException("More than one 'distinct' term found in a unitary SNF formula.")
    else if (distinctTerms.length == 1) {
      // We've got the single distinct term, return it:
      return distinctTerms(0);
    }
    null;
  }

  private def extractSpiderInequalities(spiders: Buffer[Free], conjuncts: Buffer[Term]): Unit = {
    if (spiders != null && spiders.length > 0) {
      // We need spider inequalities only if there are any spiders at all...
      val distinctTerm: Term = extractDistinctTerm(conjuncts);
    }
  }

  private def convertoToPSD(spiders: Buffer[Free], conjuncts: Buffer[Term]): SpiderDiagram = {
    // TODO: Check spider inequalities:
    extractSpiderInequalities(spiders, conjuncts);
    SpiderDiagrams.createNullSD();
  }

  private val recognise: Convertor = {
    case x => (recogniseBinaryHOLOperator
      orElse recogniseMetaAll
      orElse recogniseTrueprop
      orElse recogniseExistential
      orElse recogniseNegation
      orElse { case _ => throw new RuntimeException("Could not convert the formula to a spider diagram. Not an SNF formula.") }: Convertor)(x)
  }

  private val recogniseBinaryHOLOperator: Convertor = {
    case (App(App(Const(operator, typ), lhs), rhs), spiderType) if BinaryOperators contains operator => {
      // If this recognises the meta implications, then it will be without
      // quantified spiders. Therefore the LHS and the RHS must be just normal
      // spider diagrams in the SNF form.
      val (lhsSD, spiderType1) = recognise(lhs, spiderType);
      val (rhsSD, spiderType2) = recognise(rhs, spiderType1);
      (SpiderDiagrams.createCompoundSD(operatorsIsaToSD(operator), lhsSD, rhsSD), spiderType2);
    }
  };

  private val recogniseNegation: Convertor = {
    case (App(Const(HOLNot, typ), body), spiderType) => {
      val (negSD, spiderType1) = recognise(body, spiderType);
      (SpiderDiagrams.createCompoundSD(Negation, negSD), spiderType1);
    }
  };

  private val recogniseExistential: Convertor = {
    case (term @ App(Const(HOLExistential, typ), Abs(spider, spiderType1, body)), spiderType) => {
      if (!checkSpiderType(spiderType1, spiderType)) throw new ReadingException("Could not convert the formula into a spider diagram. Not all spiders are of the same type.");

      // Extract all spiders and the conjuncts of the body:
      val spiders = ArrayBuffer[Free]();
      val conjuncts = ArrayBuffer[Term]();
      extractConjuncts(extractSpidersAndBody(term, spiders), conjuncts);
      // Make sure that all spiders have the same type:
      if (!spiders.forall { spider => checkSpiderType(spider.typ, spiderType1) }) throw new ReadingException("Could not convert the formula into a spider diagram. Not all spiders are of the same type.");

      // Now extract the unitary spider diagram out of the data:
      (convertoToPSD(spiders, conjuncts), typ);
    }
  };

  private val recogniseTrueprop: Convertor = {
    case (App(Const(HOLTrueprop, typ), body), spiderType) => recognise(body, spiderType)
  }

  private val recogniseMetaAll: Convertor = {
    case (term @ App(Const(MetaAll, typ), Abs(spider, newSpiderType, body)), spiderType) => {
      if (!checkSpiderType(newSpiderType, spiderType)) throw new ReadingException("Could not convert the formula into a spider diagram. Not all spiders are of the same type.");

      // We have to extract all quantified spiders.
      val spiders = ArrayBuffer[Free]();
      val body = findQuantifiedVarsAndBody(term, spiders);
      // Make sure that all spiders have the same type:
      if (!spiders.forall { spiders => checkSpiderType(spiders.typ, newSpiderType) }) throw new ReadingException("Could not convert the formula into a spider diagram. Not all spiders are of the same type.");

      // Now find all premises and the conclusion:
      val premises = ArrayBuffer[Term]();
      val conclusion = findPremisesAndConclusion(body, premises);

      // Now extract all conjuncts from the premises:
      val conjuncts = ArrayBuffer[Term]();
      extractConjuncts(premises, conjuncts);

      // We've got enough info to extract a spider diagram from the premises:
      val lhsSD = convertoToPSD(spiders, conjuncts);
      val (rhsSD, _) = recognise(conclusion, newSpiderType);

      (SpiderDiagrams.createCompoundSD(Operator.Implication, lhsSD, rhsSD), newSpiderType);
    }
  }

}