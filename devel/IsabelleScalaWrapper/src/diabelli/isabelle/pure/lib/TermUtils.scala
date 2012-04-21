package diabelli.isabelle.pure.lib
import java.util.ArrayList
import java.util.List
import isabelle.Term._
import scala.collection.mutable.Buffer
import scala.collection.JavaConversions
import scala.collection.mutable.ArrayBuffer

/**
 * Provides a bunch of methods for
 */
object TermUtils {

  // Binary operators:
  val HOLConjunction = "HOL.conj";
  val HOLDisjunction = "HOL.disj";
  val HOLImplication = "HOL.implies";
  val HOLEquality = "HOL.eq";
  val MetaImplication = "==>";
  // Quantifiers:
  val HOLExistential = "HOL.Ex";
  val HOLAll = "HOL.All";
  val MetaAll = "all";
  // Unary operators:
  val HOLNot = "HOL.Not";
  val HOLTrueprop = "HOL.Trueprop";
  // Constants:
  val HOLTrue = "HOL.True";
  val HOLFalse = "HOL.False";
  // Types
  val HOLTypeBool = "HOL.bool";

  def main(args: Array[String]): Unit = {
    val premises: ArrayList[Term] = new ArrayList();
    val conclusion: Term = findPremisesAndConclusion(TermYXML.parseYXML(TermYXML.Example2_unescapedYXML), premises);
    println(conclusion);
    println(premises);
    println(premises.size());
    val variables: ArrayList[Free] = new ArrayList();
    val body: Term = findQuantifiedVarsAndBody(TermYXML.parseYXML(TermYXML.Example3_unescapedYXML), variables);
    println(body);
    println(variables);
    println(variables.size());
  }

  /**
   * Extracts the premises and the conclusion from the given term `t`. This
   * method puts the premises into the given array and returns the conclusion.
   */
  def findPremisesAndConclusion(t: Term, premises: List[Term]): Term = {
    t match {
      case App(App(Const(MetaImplication, _), lhsTerm), rhsTerm) => {
        premises.add(lhsTerm);
        findPremisesAndConclusion(rhsTerm, premises);
      }
      case _ => t
    }
  }

  /**
   * Extracts the premises and the conclusion from the given term `t`. This
   * method puts the premises into the given array and returns the conclusion.
   */
  def findPremisesAndConclusion(t: Term, premises: Buffer[Term]): Term = findPremisesAndConclusion(t, JavaConversions.asJavaList(premises))

  /**
   * Extracts the globally meta-quantified variables from the term, puts them
   * into the given array list packed as separate `Term.Free`, and returns the
   * body.
   *
   * For example, from the formula `⋀ x y z. ⟦ A(x, y, z) ⟧ ⟹ B(x, y, z)`, we
   * get `⟦ A(x, y, z) ⟧ ⟹ B(x, y, z)` as the body, and the list `[x, y, z]`
   * in the variables list.
   *
   * The quantified variables in the body are still retained as bound.
   */
  def findQuantifiedVarsAndBody(t: Term, variables: List[Free]): Term = {
    t match {
      case App(Const(MetaAll, _), Abs(varName, varType, body)) => {
        variables.add(Free(varName, varType));
        findQuantifiedVarsAndBody(body, variables);
      }
      case _ => t
    }
  }

  /**
   * Extracts the globally meta-quantified variables from the term, puts them
   * into the given array list packed as separate `Term.Free`, and returns the
   * body.
   *
   * For example, from the formula `⋀ x y z. ⟦ A(x, y, z) ⟧ ⟹ B(x, y, z)`, we
   * get `⟦ A(x, y, z) ⟧ ⟹ B(x, y, z)` as the body, and the list `[x, y, z]`
   * in the variables list.
   *
   * The quantified variables in the body are still retained as bound.
   */
  def findQuantifiedVarsAndBody(t: Term, variables: Buffer[Free]): Term = findQuantifiedVarsAndBody(t, JavaConversions.asJavaList(variables))

  /**
   * The constant name for the HOL list Cons constructor.
   */
  val HOLListCons = "List.list.Cons";

  /**
   * The constant name for the HOL list Nil constructor.
   */
  val HOLListNil = "List.list.Nil";

  /**
   * Returns the terms that represent the elements of the `listTerm` which must
   * be an HOL list.
   */
  def getListElements(listTerm: Term, outElements: List[Term]): List[Term] = {
    listTerm match {
      case App(App(Const(HOLListCons, _), element), rest) => { outElements.add(element); getListElements(rest, outElements); }
      case Const(HOLListNil, _) => {}
      case x => throw new IllegalArgumentException("The given term is not an HOL list. It contained the term '%s'.".format(x));
    }
    outElements;
  }

  /**
   * Returns the terms that represent the elements of the `listTerm` which must
   * be an HOL list.
   */
  def getListElements(listTerm: Term, outElements: Buffer[Term] = ArrayBuffer[Term]()): Buffer[Term] = {
    getListElements(listTerm, JavaConversions.asJavaList(outElements));
    outElements;
  }
}