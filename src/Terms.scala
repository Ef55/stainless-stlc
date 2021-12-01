import stainless.lang._
import stainless.collection._
import stainless.annotation._

object STLC {
  object Constants {
    sealed trait GroundType
    case object UnitType extends GroundType
    case object IntegerType extends GroundType

    sealed trait Constant
    case object Unit extends Constant
    case class Integer(i: BigInt) extends Constant { require(i >= 0) }

    def typeOf(cst: Constant): Type = {
      cst match {
        case Unit => BaseType(UnitType)
        case Integer(_) => BaseType(IntegerType)
      }
    }.ensuring(res => res.isInstanceOf[BaseType])

  }

  type Environment = List[Type]

  sealed trait Term {
    def isValue: Boolean = {
        this match {
            case Cst(_) => true
            case Abs(_, _) => true
            case _ => false
        }
    }

    def hasFreeVariable(i: BigInt): Boolean = {
      require(i >= 0)
      this match {
        case Variable(k)    => k == i
        case Cst(_)    => false
        case Abs(_, body)   => body.hasFreeVariable(i+1)
        case App(t1, t2)    => t1.hasFreeVariable(i) || t2.hasFreeVariable(i)
        case Fix(f)         => f.hasFreeVariable(i)
      }
    }.ensuring(res => res == this.hasFreeVariablesIn(i, 1))

    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      require(c >= 0)
      require(d >= 0)
      this match {
        case Variable(k)    => (c <= k) && (k < c+d)
        case Cst(_)    => false
        case Abs(_, body)   => body.hasFreeVariablesIn(c+1, d)
        case App(t1, t2)    => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
        case Fix(f)         => f.hasFreeVariablesIn(c, d)
      }
    }.ensuring(res => (d == 0) ==> !res)
  }
  case class Variable(k: BigInt) extends Term { require(k >= 0) }
  case class Cst(cst: Constants.Constant) extends Term
  case class Abs(b: Type, t: Term) extends Term
  case class App(t1: Term, t2: Term) extends Term
  case class Fix(t: Term) extends Term

  sealed trait Type
  case class BaseType(t: Constants.GroundType) extends Type
  case class ArrowType(t1: Type, t2: Type) extends Type


  def isClosed(t: Term): Boolean = {
    def rec(t: Term, c: BigInt): Boolean = {
      t match {
        case Variable(k)    => k < c
        case Cst(_)         => true
        case Abs(_, body)   => rec(body, c+1)
        case App(t1, t2)    => rec(t1, c) && rec(t2, c)
        case Fix(f)         => rec(f, c)
      }
    }

    rec(t, 0)
  }
}

object TermsProperties{
  import STLC._

  @opaque @pure
  def boundRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
    require(d1 >= 0 && d2 >= 0)
    require(c >= 0)
    require(d2 <= d1)
    require(!t.hasFreeVariablesIn(c, d1))

    t match{
      case Variable(_) => ()
      case Cst(_) => ()
      case Abs(targ, body) =>
        boundRangeDecrease(body, c + 1, d1, d2)
      case App(t1, t2) => {
        boundRangeDecrease(t1, c, d1, d2)
        boundRangeDecrease(t2, c, d1, d2)
      }
      case Fix(f) => boundRangeDecrease(f, c, d1, d2)
    }
  }.ensuring(!t.hasFreeVariablesIn(c, d2))

  @opaque @pure
  def noFreeVariablesIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
    require(c1 >= 0 && c2 >= 0)
    require(0 <= d && c2 - c1 <= d)
    require(c1 <= c2)
    require(!t.hasFreeVariablesIn(c1, d))

    t match {
      case Variable(_) => ()
      case Cst(_) => ()
      case Abs(targ, body) => noFreeVariablesIncreaseCutoff(body, c1 + 1, c2 + 1, d)
      case App(t1, t2) => {
        noFreeVariablesIncreaseCutoff(t1, c1, c2, d)
        noFreeVariablesIncreaseCutoff(t2, c1, c2, d)
      }
      case Fix(f) => noFreeVariablesIncreaseCutoff(f, c1, c2, d)
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
      case Variable(k) => ()
      case Cst(_) => ()
      case Abs(targ, body) =>
        boundRangeConcatenation(body, a + 1, b, c)
      case App(t1, t2) => {
        boundRangeConcatenation(t1, a, b, c)
        boundRangeConcatenation(t2, a, b, c)
      }
      case Fix(f) => boundRangeConcatenation(f, a, b, c)
    }
  }.ensuring(!t.hasFreeVariablesIn(a, b + c))

  @opaque @pure
  def boundRangeSinglize(t: Term, j: BigInt, d: BigInt, i: BigInt): Unit = {
    require(j >= 0)
    require(d >= 0)
    require(j <= i && i < j+d)
    require(!t.hasFreeVariablesIn(j, d))

    t match {
      case Variable(_) => assert(!t.hasFreeVariable(i))
      case Cst(_) => assert(!t.hasFreeVariable(i))
      case Abs(_, body) => {
        boundRangeSinglize(body, j+1, d, i+1)
        assert(!t.hasFreeVariable(i))
      }
      case App(t1, t2) => {
        boundRangeSinglize(t1, j, d, i)
        boundRangeSinglize(t2, j, d, i)
        assert(!t.hasFreeVariable(i))
      }
      case Fix(f) => boundRangeSinglize(f, j, d, i)
    }
  }.ensuring(!t.hasFreeVariable(i))
}