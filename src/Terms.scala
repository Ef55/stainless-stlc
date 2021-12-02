import stainless.lang._
import stainless.collection._
import stainless.annotation._

object STLC {
  sealed trait Type
  case class BasicType(s: String) extends Type
  case class ArrowType(t1: Type, t2: Type) extends Type

  type Environment = List[Type]

  sealed trait Term {
    def isValue: Boolean = {
        this match {
            case Abs(_, _) => true
            case _ => false
        }
    }

    def hasFreeVar(i: BigInt): Boolean = {
      require(i >= 0)
      this match {
        case Var(k)         => k == i
        case Abs(_, body)   => body.hasFreeVar(i+1)
        case App(t1, t2)    => t1.hasFreeVar(i) || t2.hasFreeVar(i)
        case Fix(f)         => f.hasFreeVar(i)
      }
    }.ensuring(res => res == this.hasFreeVarsIn(i, 1))

    def hasFreeVarsIn(c: BigInt, d: BigInt): Boolean = {
      require(c >= 0)
      require(d >= 0)
      this match {
        case Var(k)         => (c <= k) && (k < c+d)
        case Abs(_, body)   => body.hasFreeVarsIn(c+1, d)
        case App(t1, t2)    => t1.hasFreeVarsIn(c, d) || t2.hasFreeVarsIn(c, d)
        case Fix(f)         => f.hasFreeVarsIn(c, d)
      }
    }.ensuring(res => (d == 0) ==> !res)

    def isClosed: Boolean = {
      def rec(t: Term, c: BigInt): Boolean = {
        t match {
          case Var(k)         => k < c
          case Abs(_, body)   => rec(body, c+1)
          case App(t1, t2)    => rec(t1, c) && rec(t2, c)
          case Fix(f)         => rec(f, c)
        }
      }

      rec(this, 0)
    }
  }
  case class Var(k: BigInt) extends Term { require(k >= 0) }
  case class Abs(b: Type, t: Term) extends Term
  case class App(t1: Term, t2: Term) extends Term
  case class Fix(t: Term) extends Term

}

object TermsProperties{
  import STLC._

  @opaque @pure
  def boundRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
    require(d1 >= 0 && d2 >= 0)
    require(c >= 0)
    require(d2 <= d1)
    require(!t.hasFreeVarsIn(c, d1))

    t match{
      case Var(_) => ()
      case Abs(targ, body) => {
        boundRangeDecrease(body, c + 1, d1, d2)
      }
      case App(t1, t2) => {
        boundRangeDecrease(t1, c, d1, d2)
        boundRangeDecrease(t2, c, d1, d2)
      }
      case Fix(f) => boundRangeDecrease(f, c, d1, d2)
    }
  }.ensuring(!t.hasFreeVarsIn(c, d2))

  @opaque @pure
  def noFreeVarsIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
    require(c1 >= 0 && c2 >= 0)
    require(0 <= d && c2 - c1 <= d)
    require(c1 <= c2)
    require(!t.hasFreeVarsIn(c1, d))

    t match {
      case Var(_) => ()
      case Abs(targ, body) => noFreeVarsIncreaseCutoff(body, c1 + 1, c2 + 1, d)
      case App(t1, t2) => {
        noFreeVarsIncreaseCutoff(t1, c1, c2, d)
        noFreeVarsIncreaseCutoff(t2, c1, c2, d)
      }
      case Fix(f) => noFreeVarsIncreaseCutoff(f, c1, c2, d)
    }
  }.ensuring(!t.hasFreeVarsIn(c2, d - (c2 - c1)))

  @opaque @pure
  def boundRangeConcatenation(t: Term, a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(!t.hasFreeVarsIn(a, b))
    require(!t.hasFreeVarsIn(a + b, c))

    t match{
      case Var(k) => ()
      case Abs(targ, body) => {
        boundRangeConcatenation(body, a + 1, b, c)
      }
      case App(t1, t2) => {
        boundRangeConcatenation(t1, a, b, c)
        boundRangeConcatenation(t2, a, b, c)
      }
      case Fix(f) => boundRangeConcatenation(f, a, b, c)
    }
  }.ensuring(!t.hasFreeVarsIn(a, b + c))

  @opaque @pure
  def boundRangeSinglize(t: Term, j: BigInt, d: BigInt, i: BigInt): Unit = {
    require(j >= 0)
    require(d >= 0)
    require(j <= i && i < j+d)
    require(!t.hasFreeVarsIn(j, d))

    t match {
      case Var(_) => assert(!t.hasFreeVar(i))
      case Abs(_, body) => {
        boundRangeSinglize(body, j+1, d, i+1)
        assert(!t.hasFreeVar(i))
      }
      case App(t1, t2) => {
        boundRangeSinglize(t1, j, d, i)
        boundRangeSinglize(t2, j, d, i)
        assert(!t.hasFreeVar(i))
      }
      case Fix(f) => boundRangeSinglize(f, j, d, i)
    }
  }.ensuring(!t.hasFreeVar(i))
}