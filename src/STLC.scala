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
            case _         => false
        }
    }

    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      require(c >= 0)
      require(d >= 0)
      this match {
        case Var(k)         => (c <= k) && (k < c+d)
        case Abs(_, body)   => body.hasFreeVariablesIn(c+1, d)
        case App(t1, t2)    => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
        case Fix(f)         => f.hasFreeVariablesIn(c, d)
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
  case class Abs(argType: Type, body: Term) extends Term
  case class App(t1: Term, t2: Term) extends Term
  case class Fix(t: Term) extends Term

}

object STLCProperties{
  import STLC._

  object Terms {
    @opaque @pure
    def boundRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      require(d1 >= 0 && d2 >= 0)
      require(c >= 0)
      require(d2 <= d1)
      require(!t.hasFreeVariablesIn(c, d1))

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
    }.ensuring(!t.hasFreeVariablesIn(c, d2))

    @opaque @pure
    def boundRangeIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      require(c1 >= 0 && c2 >= 0)
      require(0 <= d && c2 - c1 <= d)
      require(c1 <= c2)
      require(!t.hasFreeVariablesIn(c1, d))

      t match {
        case Var(_) => ()
        case Abs(targ, body) => boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
        case App(t1, t2) => {
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        }
        case Fix(f) => boundRangeIncreaseCutoff(f, c1, c2, d)
      }
    }.ensuring(!t.hasFreeVariablesIn(c2, d - (c2 - c1)))

    @opaque @pure
    def boundRangeConcatenation(t: Term, a: BigInt, b: BigInt, c: BigInt): Unit = {
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(!t.hasFreeVariablesIn(a + b, c))

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
    }.ensuring(!t.hasFreeVariablesIn(a, b + c))
  }

}