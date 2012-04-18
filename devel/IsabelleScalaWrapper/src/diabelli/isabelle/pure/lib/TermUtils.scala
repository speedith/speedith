package diabelli.isabelle.pure.lib
import java.util.ArrayList
import isabelle.Term

/**
 * Provides a bunch of methods for
 */
object TermUtils {

  val HOLConjunction = "HOL.conj";
  val HOLDisjunction = "HOL.disj";
  val HOLImplication = "HOL.implies";
  val HOLEquality = "HOL.eq";
  val HOLExistential = "HOL.Ex";
  val HOLAll = "HOL.All";
  val HOLNot = "HOL.Not";
  val HOLTrue = "HOL.True";
  val HOLFalse = "HOL.False";
  val HOLTrueprop = "HOL.Trueprop";
  val MetaImplication = "==>";
  val MetaAll = "all";

  def main(args: Array[String]): Unit = {
    val premises: ArrayList[Term.Term] = new ArrayList();
    val conclusion: Term.Term = findPremisesAndConclusion(TermYXML.parseYXML(TermYXML.Example2_unescapedYXML), premises);
    println(conclusion);
    println(premises);
    println(premises.size());
    val variables: ArrayList[Term.Free] = new ArrayList();
    val body: Term.Term = findQuantifiedVarsAndBody(TermYXML.parseYXML(TermYXML.Example3_unescapedYXML), variables);
    println(body);
    println(variables);
    println(variables.size());
  }

  /**
   * Extracts the premises and the conclusion from the given term `t`. This
   * method puts the premises into the given array and returns the conclusion.
   */
  def findPremisesAndConclusion(t: Term.Term, premises: ArrayList[Term.Term]): Term.Term = {
    t match {
      case Term.App(Term.App(Term.Const(MetaImplication, _), lhsTerm), rhsTerm) => {
        premises.add(lhsTerm);
        findPremisesAndConclusion(rhsTerm, premises);
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
  def findQuantifiedVarsAndBody(t: Term.Term, variables: ArrayList[Term.Free]): Term.Term = {
    t match {
      case Term.App(Term.Const(MetaAll, _), Term.Abs(varName, varType, body)) => {
        variables.add(Term.Free(varName, varType));
        findQuantifiedVarsAndBody(body, variables);
      }
      case _ => t
    }
  }
}