package speedith.diabelli.isabelle
import isabelle.Term._
import speedith.core.lang.Region
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
import scala.collection.mutable.HashSet
import scala.collection.mutable.Buffer
import scala.collection.LinearSeq
import speedith.core.lang.PrimarySpiderDiagram
import diabelli.isabelle.pure.lib.TermUtils

object Translations {

  /**
   * This main method is used only for testing.
   */
  def main(args: Array[String]): Unit = {
    var sd: SpiderDiagram = termToSpiderDiagram(parseYXML(Example6_unescapedYXML));
    println(sd);
    sd = termToSpiderDiagram(parseYXML(Example7_unescapedYXML));
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
    recognise(t, null)._1;
  }

  // Everything below here is just translation implementation detail.

  // RECOGNISERS: Just functions of a special type that convert Isabelle terms to spider diagrams.
  private type RecogniserIn = ( /*term:*/ Term, /*spiderType:*/ Typ);
  private type RecogniserOut = (SpiderDiagram, /*spiderType:*/ Typ);
  private type Recogniser = PartialFunction[RecogniserIn, RecogniserOut];

  private val recognise: Recogniser = {
    case x => (recogniseBinaryHOLOperator
      orElse recogniseMetaAll
      orElse recogniseTrueprop
      orElse recogniseExistential
      orElse recogniseNegation
      orElse { case _ => throw new RuntimeException("Could not convert the formula to a spider diagram. Not an SNF formula.") }: Recogniser)(x)
  }

  private val recogniseBinaryHOLOperator: Recogniser = {
    case (App(App(Const(operator, typ), lhs), rhs), spiderType) if BinaryOperators contains operator => {
      // If this recognises the meta implications, then it will be without
      // quantified spiders. Therefore the LHS and the RHS must be just normal
      // spider diagrams in the SNF form.
      val (lhsSD, spiderType1) = recognise(lhs, spiderType);
      val (rhsSD, spiderType2) = recognise(rhs, spiderType1);
      (SpiderDiagrams.createCompoundSD(operatorsIsaToSD(operator), lhsSD, rhsSD), spiderType2);
    }
  };

  private val recogniseNegation: Recogniser = {
    case (App(Const(HOLNot, typ), body), spiderType) => {
      val (negSD, spiderType1) = recognise(body, spiderType);
      (SpiderDiagrams.createCompoundSD(Negation, negSD), spiderType1);
    }
  };

  private val recogniseExistential: Recogniser = {
    case (term @ App(Const(HOLExistential, typ), Abs(spider, spiderType1, body)), spiderType) => {
      if (!checkSpiderType(spiderType1, spiderType)) throw new ReadingException("Not all spiders are of the same type.");

      // Extract all spiders and the conjuncts of the body:
      val spiders = ArrayBuffer[Free]();
      val conjuncts = ArrayBuffer[Term]();
      extractConjuncts(extractSpidersAndBody(term, spiders), conjuncts);
      // Make sure that all spiders have the same type:
      if (!spiders.forall { spider => checkSpiderType(spider.typ, spiderType1) }) throw new ReadingException("Not all spiders are of the same type.");

      // Now extract the unitary spider diagram out of the data:
      convertoToPSD(spiders, spiderType1, conjuncts);
    }
  };

  private val recogniseTrueprop: Recogniser = {
    case (App(Const(HOLTrueprop, typ), body), spiderType) => recognise(body, spiderType)
  }

  private val recogniseMetaAll: Recogniser = {
    case (term @ App(Const(MetaAll, typ), Abs(spider, spiderType1, body)), spiderType) => {
      if (!checkSpiderType(spiderType1, spiderType)) throw new ReadingException("Not all spiders are of the same type.");

      // We have to extract all quantified spiders.
      val spiders = ArrayBuffer[Free]();
      val body = findQuantifiedVarsAndBody(term, spiders);
      // Make sure that all spiders have the same type:
      if (!spiders.forall { spiders => checkSpiderType(spiders.typ, spiderType1) }) throw new ReadingException("Not all spiders are of the same type.");

      // Now find all premises and the conclusion:
      val premises = ArrayBuffer[Term]();
      val conclusion = findPremisesAndConclusion(body, premises);

      // Now extract all conjuncts from the premises:
      val conjuncts = ArrayBuffer[Term]();
      extractConjuncts(premises, conjuncts);

      // We've got enough info to extract a spider diagram from the premises:
      val (lhsSD, spiderType2) = convertoToPSD(spiders, spiderType1, conjuncts);
      val (rhsSD, spiderType3) = recognise(conclusion, spiderType2);

      (SpiderDiagrams.createCompoundSD(Implication, lhsSD, rhsSD), spiderType3);
    }
  }

  // HELPER FUNCTIONS
  private val BinaryOperators = Set(HOLConjunction, HOLDisjunction, HOLImplication, HOLEquality, MetaImplication);

  private val HOLListDistinct = "List.distinct";
  private val HOLSetMember = "Set.member";
  private val HOLSetDifference = "Groups.minus_class.minus";
  private val HOLSetComplement = "Groups.uminus_class.uminus";
  private val HOLSetIntersection = "Lattices.inf_class.inf";
  private val HOLSetUnion = "Lattices.sup_class.sup";

  private def getAndRemove[A, T <: A, B](buffer: Buffer[T], filter: A => Option[B]): ArrayBuffer[B] = {
    val retVal = ArrayBuffer[B]();
    var i = 0;
    while (i < buffer.length) {
      filter(buffer(i)) match {
        case Some(x) => buffer.remove(i); retVal += x;
        case None => i = i + 1;
      }
    }
    retVal;
  }

  private def rlRemoveWhere[A, T <: A](buffer: Buffer[T], filter: A => Boolean): Unit = {
    var i = buffer.length - 1;
    while (i >= 0) {
      if (filter(buffer(i))) {
        buffer.remove(i);
      }
      i = i - 1;
    }
  }

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
  private def extractSpidersAndBody(t: Term, variables: Buffer[Free]): Term = {
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

  private def extractDistinctTerm(conjuncts: Buffer[Term]): App = {
    val distinctTerms = getAndRemove(conjuncts, (t: Term) => t match { case x @ App(Const(HOLListDistinct, _), _) => Some(x); case _ => None; });
    if (distinctTerms.length > 1) throw new ReadingException("More than one 'distinct' term found in a unitary SNF formula.")
    else if (distinctTerms.length == 1) {
      // We've got the single distinct term, return it:
      return distinctTerms(0);
    }
    null;
  }

  private def extractSpiderInequalities(conjuncts: Buffer[Term], spiders: Buffer[Free]): Boolean = {
    if (spiders != null && spiders.length > 1) {
      val inequalities = new Array[Boolean](spiders.length * spiders.length);
      val spiderType = spiders(0).typ;
      rlRemoveWhere(conjuncts, (t: Term) => {
        t match {
          case App(Const(HOLNot, _), App(App(Const(HOLEquality, Type(_, List(spiderType1, Type(_, List(spiderType2, _))))), Bound(spider1)), Bound(spider2))) if spiderType1.equals(spiderType2) && checkSpiderType(spiderType1, spiderType) => {
            inequalities(Math.min(spider1, spider2) * spiders.length + Math.max(spider1, spider2)) = true;
            true;
          }
          case _ => false;
        }
      });
      for (i <- 0 to spiders.length - 1) {
        for (j <- i + 1 to spiders.length - 1) {
          if (!inequalities(i * spiders.length + j)) return false;
        }
      }
      return true;
    } else false;
  }

  private def checkSpiderInequalities(spiders: Buffer[Free], conjuncts: Buffer[Term]): Unit = {
    if (spiders != null && spiders.length > 1) {
      // We need spider inequalities only if there are at least two spiders...
      // Is there a distinct term present?
      
      val inequalitiesPresent = extractSpiderInequalities(conjuncts, spiders);
      // If the user specified inequalities, then that's fine. But if
      // inequalities are not specified, then let's look for the distinct clause:
      if (!inequalitiesPresent) {
        val distinctTerm: App = extractDistinctTerm(conjuncts);
        if (distinctTerm == null) {
          // There is no `distinct` term and no equalities. This is not allowed:
          throw new ReadingException("Did not find a 'distinct' assertion. This is needed to tell that spiders are distinct elements.");
        } else {
          // If there is a `distinct` term, check that it contains all spiders:
          val distincts = TermUtils.getListElements(distinctTerm.arg) map { case Bound(i) => spiders(spiders.length - i - 1); case _ => throw new ReadingException("The 'distinct' term does not contain only spiders.") } toSet;
          if (spiders exists (s => !distincts.contains(s))) throw new ReadingException("The 'distinct' assertion does not contain all spiders.");
          // Okay, all spiders are distinct...
        }
      }
    }
  }

  private def findContoursInTerm(term: Term, spiderType: Typ, outContours: HashSet[Free] = HashSet[Free]()): Typ = {
    term match {
      case t @ Free(predicateName, Type(fun, List(spiderType1, Type(HOLTypeBool, List())))) => {
        if (!checkSpiderType(spiderType1, spiderType)) throw new ReadingException("A contour's type '%s' does not match the spider's type '%s'.".format(spiderType1, spiderType));
        outContours += t;
        spiderType1;
      }
      case Abs(_, _, body) => findContoursInTerm(body, spiderType, outContours);
      case App(lhs, rhs) => { findContours(List(lhs, rhs), spiderType, outContours)._2; }
      case _ => spiderType;
    }
  }

  private def findContours(conjuncts: Seq[Term], spiderType: Typ, outContours: HashSet[Free] = HashSet[Free]()): (HashSet[Free], Typ) = {
    var spiderType1 = spiderType;
    for (t <- conjuncts) { spiderType1 = findContoursInTerm(t, spiderType1, outContours); }
    (outContours, spiderType);
  }

  /**
   * Returns the spider at the 'from-behind' index (i.e.: index `0` maps to
   * `length - 1` and index `length - 1` maps to `0`).
   */
  private def getSpiderWithBoundIndex(boundIndex: Int, spiders: Buffer[Free]): Free = spiders(spiders.length - 1 - boundIndex);

  private def extractHabitat(t: Term, spiders: Buffer[Free], contours: HashSet[Term], spiderType: Typ, habitats: HashMap[Free, Region]): (Boolean, Typ) = {
    t match {
      case App(App(Const(HOLSetMember, _), Bound(spiderIndex)), region) => {
        val spider = getSpiderWithBoundIndex(spiderIndex, spiders);
        if (habitats.contains(spider)) throw new ReadingException("The spider '%s' has two regions. Only one region may be specified for a given spider.");
        (true, spiderType);
      }
      case _ => (false, spiderType);
    }
  }

  def extractHabitatTermsForSpider(spiderIndex: Int, conjuncts: Buffer[Term], habitatTerms: ArrayBuffer[Term] = ArrayBuffer()): ArrayBuffer[Term] = {
    var i = conjuncts.length - 1;
    while (i >= 0) {
      conjuncts(i) match {
        case App(App(Const(HOLSetMember, _), Bound(boundIndex)), region) if boundIndex == spiderIndex => habitatTerms += region; conjuncts.remove(i);
        case _ =>
      }
      i = i - 1;
    }
    habitatTerms;
  }

  private def extractHabitats(conjuncts: Buffer[Term], spiders: Buffer[Free], contours: HashSet[Free], spiderType: Typ, habitats: HashMap[Free, Region] = HashMap()): (HashMap[Free, Region], Typ) = {
    // For each spider, find all the terms that talk about its set membership:
    for (spiderIndex <- 0 to spiders.length - 1) {
      val habitatTerms = extractHabitatTermsForSpider(spiderIndex, conjuncts);
    }
    (habitats, spiderType);
  }

  private def convertoToPSD(spiders: Buffer[Free], spiderType: Typ, conjuncts: Buffer[Term]): (SpiderDiagram, Typ) = {
    // Check spider inequalities:
    checkSpiderInequalities(spiders, conjuncts);

    // Get all contour names mentioned in this unitary spider diagram, the
    // predicates are of this form:
    //		Free(B,Type(fun,List(<spiderType>, Type(HOL.bool,List()))))
    val (contours, spiderType1) = findContours(conjuncts, spiderType);
    
    println(contours.map(f => f.name));

    // Get spider habitats:
    val (habitats, spiderType2) = extractHabitats(conjuncts, spiders, contours, spiderType1);

    (SpiderDiagrams.createNullSD(), spiderType1);
  }

}