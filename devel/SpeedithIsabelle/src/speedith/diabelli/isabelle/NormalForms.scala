package speedith.diabelli.isabelle
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.HashSet

object NormalForms {

  implicit def string2atom(str: String): Formula[String] = Atom(str);

  def main(args: Array[String]): Unit = {
    val P = Atom("P");
    val Q = Atom("Q");
    val R = Atom("R");
    val S = Atom("S");
    test(¬(P ∧ Q) ∨ (Q ∧ P));
    test(¬(P) ∧ (Q ∨ R) ∧ S);
  }

  def test[A](formula: Formula[A]): Unit = {
    println("Testing formula: %s".format(formula));
    if (!toNNF(formula).isNNF()) throw new RuntimeException();
    println("NNF: " + toNNF(formula));
    if (!toCNF(formula).isCNF()) throw new RuntimeException();
    println("CNF: " + toCNF(formula));
    if (!toDNF(formula).isDNF()) throw new RuntimeException();
    println("DNF: " + toDNF(formula));
  }

  def ¬[A](formula: Formula[A]): Formula[A] = -formula;

  sealed abstract class Formula[+A] {
    def +[B >: A](that: Formula[B]): Formula[B] = Sup(this, that);
    def *[B >: A](that: Formula[B]): Formula[B] = Inf(this, that);
    def unary_-(): Formula[A] = Neg(this);
    def ∧[B >: A](that: Formula[B]): Formula[B] = this * that;
    def ∨[B >: A](that: Formula[B]): Formula[B] = this + that;
    def isLiteral(): Boolean = false;
    def isCNF(): Boolean;
    def isDNF(): Boolean;
    def isNNF(): Boolean;
  }

  case class Inf[+A](lhs: Formula[A], rhs: Formula[A]) extends Formula[A] {
    override def toString(): String = {
      val lhsStr = lhs match {
        case Sup(_, _) => "(" + lhs.toString() + ")";
        case _ => lhs.toString();
      }
      val rhsStr = rhs match {
        case Sup(_, _) => "(" + rhs.toString() + ")";
        case _ => rhs.toString();
      }
      lhsStr + " \u2227 " + rhsStr;
    }
    /**
     * This formula is in CNF if and only if its children are in CNF.
     */
    def isCNF(): Boolean = { lhs.isCNF() && rhs.isCNF(); }
    /**
     * This formula is in DNF if and only if it contains no Sup(_, _) children
     * and all children must be in DNF.
     */
    def isDNF(): Boolean = this match {
      case Inf(Sup(_, _), _) | Inf(_, Sup(_, _)) => false;
      case _ => lhs.isDNF() && rhs.isDNF();
    }
    def isNNF(): Boolean = lhs.isNNF() && rhs.isNNF();
  }

  case class Sup[+A](lhs: Formula[A], rhs: Formula[A]) extends Formula[A] {
    override def toString(): String = "%s \u2228 %s".format(lhs.toString(), rhs.toString());
    /**
     * This formula is in CNF if and only if it contains no Inf(_, _) children
     * and all children must be in CNF.
     */
    def isCNF(): Boolean = this match {
      case Sup(Inf(_, _), _) | Sup(_, Inf(_, _)) => false;
      case _ => lhs.isCNF() && rhs.isCNF();
    }
    /**
     * This formula is in DNF if and only if its children are in DNF.
     */
    def isDNF(): Boolean = { lhs.isDNF() && rhs.isDNF(); }
    def isNNF(): Boolean = lhs.isNNF() && rhs.isNNF();
  }

  case class Neg[+A](body: Formula[A]) extends Formula[A] {
    override def toString(): String = {
      body match {
        case Neg(_) | Atom(_) => "¬" + body.toString();
        case _ => "¬(%s)".format(body);
      }
    }
    override def isLiteral(): Boolean = { body match { case Atom(_) => true; case _ => false; } }
    def isNNF(): Boolean = isLiteral();
    def isCNF(): Boolean = isLiteral();
    def isDNF(): Boolean = isLiteral();
  }

  case class Atom[+A](val atom: A) extends Formula[A] {
    override def toString(): String = atom.toString();
    override def isLiteral(): Boolean = true;
    def isCNF(): Boolean = { true; }
    def isDNF(): Boolean = { true; }
    def isNNF(): Boolean = { true; }
  }

  def toConjuncts[A, B](conjuncts: Seq[B], convertor: B => Formula[A]) = {
    if (conjuncts == null || conjuncts.length < 1)
      null;
    else
      ((null: Formula[A]) /: conjuncts)((x, y) => if (x == null) convertor(y) else Inf(x, convertor(y)));
  }

  def toNNF[A](formula: Formula[A]): Formula[A] = {
    formula match {
      case Inf(lhs, rhs) => Inf(toNNF(lhs), toNNF(rhs));
      case Sup(lhs, rhs) => Sup(toNNF(lhs), toNNF(rhs));
      case Neg(Inf(lhs, rhs)) => Sup(toNNF(Neg(lhs)), toNNF(Neg(rhs)));
      case Neg(Sup(lhs, rhs)) => Inf(toNNF(Neg(lhs)), toNNF(Neg(rhs)));
      case Neg(Neg(body)) => toNNF(body);
      case Neg(Atom(body)) => formula;
      case Atom(x) => formula;
    }
  }

  def toCNF[A](formula: Formula[A]): Formula[A] = {
    val nnf = toNNF(formula);
    def toCNFImpl(nnfFormula: Formula[A]): Formula[A] = {
      nnfFormula match {
        case Sup(Inf(a, b), Inf(c, d)) => Inf(Inf(toCNFImpl(Sup(a, c)),toCNFImpl(Sup(a, d))), Inf(toCNFImpl(Sup(b, c)),toCNFImpl(Sup(b, d))));
        case Sup(a, Inf(b, c)) => Inf(toCNFImpl(Sup(a, b)), toCNFImpl(Sup(a, c)));
        case Sup(Inf(b, c), a) => Inf(toCNFImpl(Sup(b, a)), toCNFImpl(Sup(c, a)));
        case t @ Sup(a, b) if !t.isCNF => toCNFImpl(Sup(toCNFImpl(a), toCNFImpl(b)));
        case t @ Inf(a, b) if !t.isCNF => Inf(toCNFImpl(a), toCNFImpl(b));
        case x => x;
      }
    }
    toCNFImpl(nnf);
  }

  def toDNF[A](formula: Formula[A]): Formula[A] = {
    val nnf = toNNF(formula);
    def toDNFImpl(nnfFormula: Formula[A]): Formula[A] = {
      nnfFormula match {
        case Inf(Sup(a, b), Sup(c, d)) => Sup(Sup(toDNFImpl(Inf(a, c)),toDNFImpl(Inf(a, d))), Sup(toDNFImpl(Inf(b, c)),toDNFImpl(Inf(b, d))));
        case Inf(a, Sup(b, c)) => Sup(toDNFImpl(Inf(a, b)), toDNFImpl(Inf(a, c)));
        case Inf(Sup(b, c), a) => Sup(toDNFImpl(Inf(b, a)), toDNFImpl(Inf(c, a)));
        case t @ Inf(a, b) if !t.isDNF => toDNFImpl(Inf(toDNFImpl(a), toDNFImpl(b)));
        case t @ Sup(a, b) if !t.isDNF => Sup(toDNFImpl(a), toDNFImpl(b));
        case x => x;
      }
    }
    toDNFImpl(nnf);
  }

  def extractDistincsDisjuncts[A](formula: Formula[A], terms: HashSet[Formula[A]] = HashSet[Formula[A]]()): HashSet[Formula[A]] = {
    formula match {
      case Sup(Sup(a, b), c) => extractDistincsDisjuncts(a, terms); extractDistincsDisjuncts(b, terms); extractDistincsDisjuncts(c, terms);
      case Sup(a, Sup(b, c)) => extractDistincsDisjuncts(a, terms); extractDistincsDisjuncts(b, terms); extractDistincsDisjuncts(c, terms);
      case Sup(lhs, rhs) => terms += lhs; terms += rhs;
      case x => terms += x;
    }
    terms;
  }

  def extractDisjuncts[A](formula: Formula[A], terms: ArrayBuffer[Formula[A]] = ArrayBuffer[Formula[A]]()): ArrayBuffer[Formula[A]] = {
    formula match {
      case Sup(Sup(a, b), c) => extractDisjuncts(a, terms); extractDisjuncts(b, terms); extractDisjuncts(c, terms);
      case Sup(a, Sup(b, c)) => extractDisjuncts(a, terms); extractDisjuncts(b, terms); extractDisjuncts(c, terms);
      case Sup(lhs, rhs) => terms += lhs; terms += rhs;
      case x => terms += x;
    }
    terms;
  }

  def extractDistincsConjuncts[A](formula: Formula[A], terms: HashSet[Formula[A]] = HashSet[Formula[A]]()): HashSet[Formula[A]] = {
    formula match {
      case Inf(Inf(a, b), c) => extractDistincsConjuncts(a, terms); extractDistincsConjuncts(b, terms); extractDistincsConjuncts(c, terms);
      case Inf(a, Inf(b, c)) => extractDistincsConjuncts(a, terms); extractDistincsConjuncts(b, terms); extractDistincsConjuncts(c, terms);
      case Inf(lhs, rhs) => terms += lhs; terms += rhs;
      case x => terms += x;
    }
    terms;
  }

  def extractConjuncts[A](formula: Formula[A], terms: ArrayBuffer[Formula[A]] = ArrayBuffer[Formula[A]]()): ArrayBuffer[Formula[A]] = {
    formula match {
      case Inf(Inf(a, b), c) => extractConjuncts(a, terms); extractConjuncts(b, terms); extractConjuncts(c, terms);
      case Inf(a, Inf(b, c)) => extractConjuncts(a, terms); extractConjuncts(b, terms); extractConjuncts(c, terms);
      case Inf(lhs, rhs) => terms += lhs; terms += rhs;
      case x => terms += x;
    }
    terms;
  }

}