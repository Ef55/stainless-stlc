import stainless.lang._

import SystemF._
import Reduction._
import Typing._

import org.scalatest._
import flatspec._

class ChurchTests extends AnyFlatSpec {
  def reduce(t: Term): Term = {
    require(deriveType(t).isDefined)
    var current: Term = t
    var next: Option[Term] = Some(t)
    while(next.isDefined) {
      current = next.get
      next = reduceCallByValue(current)
    }
    current
  }
  
  val unitType = UniversalType(ArrowType(VariableType(0), VariableType(0)))
  val boolType = UniversalType(ArrowType(VariableType(0), ArrowType(VariableType(0), VariableType(0))))
  val natType = UniversalType(ArrowType(ArrowType(VariableType(0), VariableType(0)), ArrowType(VariableType(0), VariableType(0))))

  val unit = TAbs(Abs(VariableType(0), Var(0)))
  val truw = TAbs(Abs(VariableType(0), Abs(VariableType(0), Var(1))))
  val falz = TAbs(Abs(VariableType(0), Abs(VariableType(0), Var(0))))
  val zero = TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), Var(0))))

  val succ = Abs(natType, TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), 
    App(Var(1), App(App(TApp(Var(2), VariableType(0)), Var(1)), Var(0)))
  ))))
  val isZero = Abs(natType, TAbs(
    App(App(TApp(Var(0), 
      boolType.t), 
      Abs(boolType.t, TApp(falz, VariableType(0)))), 
      TApp(truw, VariableType(0)))
  ))
  val add = Abs(natType, Abs(natType,
    TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), 
      App(App(TApp(Var(3), VariableType(0)), Var(1)), App(App(TApp(Var(2), VariableType(0)), Var(1)), Var(0)))
    )))
  ))

  def toChurch(b: Boolean): Term = {
    if (b) truw else falz
  }.ensuring(t => 
    (deriveType(t).get.t == boolType) &&
    t.isValue
  )

  def toChurch(n: Int): Term = {
    require(n >= 0)

    TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), 
      if(n == 0) Var(0) else App(Var(1), App(App(TApp(toChurch(n-1), VariableType(0)), Var(1)), Var(0)))
    )))
  }.ensuring(t => 
    (deriveType(t).get.t == natType) &&
    t.isValue
  )

  def booleanEquivalent(t: Term, expected: Boolean): Unit = {
    require(deriveType(t).get.t == boolType)

    assert( reduce(truw) != reduce(falz) )
    assert( reduce(App(App(TApp(t, boolType), truw), falz)) == toChurch(expected) )
  }

  def natEquivalent(t: Term, expected: Int): Unit = {
    require(deriveType(t).get.t == natType)

    assert( reduce(App(succ, zero)) != reduce(zero) )
    assert( reduce(App(App(TApp(t, natType), succ), zero)) == toChurch(expected) )
  }

  "Constants" should "have expected type" in {
    def isValueWithType(t: Term, typ: Type): Unit = {
      assert(t.isValue)
      assert(deriveType(t).get.t == typ)
      assert(reduceCallByValue(t).isEmpty)
    }

    isValueWithType(unit, unitType)
    isValueWithType(truw, boolType)
    isValueWithType(falz, boolType)
    isValueWithType(zero, natType)
    isValueWithType(succ, ArrowType(natType, natType))
    isValueWithType(add, ArrowType(natType, ArrowType(natType, natType)))
    isValueWithType(isZero, ArrowType(natType, boolType))
  }

  "Booleans" should "be distinguishable" in {
    // Sanity
    booleanEquivalent(truw, true)
    booleanEquivalent(falz, false)

    // Syntactically distinguished
    assert(truw != falz)

    // Behavioraly distinguishable
    assert( reduce(App(App(TApp(truw, boolType), truw), falz)) != reduce(App(App(TApp(falz, boolType), truw), falz)) )
    assert( reduce(App(App(TApp(truw, boolType), falz), truw)) != reduce(App(App(TApp(falz, boolType), falz), truw)) )
  }

  "Succ" should "return the expected natural" in {
    def apply(n: Term): Term = {
      require(deriveType(n).get.t == natType)

      App(succ, n)
    }.ensuring(deriveType(_).get.t == natType)


    natEquivalent(apply(zero), 1)
    natEquivalent(apply(toChurch(1)), 2)
    natEquivalent(apply(toChurch(10)), 11)
  }

  "Add" should "return the expected natural" in {
    def apply(n: Term, m: Term): Term = {
      require(deriveType(n).get.t == natType)
      require(deriveType(m).get.t == natType)

      App(App(add, n), m)
    }

    def test(n: Int, ns: Int*): Unit = {
      val addition = ns.foldLeft(toChurch(n))((n, m) => apply(n, toChurch(m)))
      val sum = ns.foldLeft(n)(_ + _)

      natEquivalent(addition, sum)
    }

    test(0, 0)
    test(0, 1)
    test(1, 0)
    test(2, 3)
    test(1, 1, 1)
    test(1, 2, 3)
    test(0, 0, 0, 0)
  }

  "IsZero" should "return the expected boolean" in {
    def apply(n: Term): Term = {
      require(deriveType(n).get.t == natType)

      App(isZero, n)
    }

    booleanEquivalent(apply(zero), true)
    booleanEquivalent(apply(toChurch(0)), true)
    booleanEquivalent(apply(toChurch(1)), false)
    booleanEquivalent(apply(toChurch(10)), false)
  }

  it should "compose correctly with IsZero" in {
    def suc(n: Term): Term = {
      require(deriveType(n).get.t == natType)

      App(isZero, App(succ, n))
    }.ensuring(deriveType(_).get.t == boolType)

    def ad(n: Term, m: Term): Term = {
      require(deriveType(n).get.t == natType)
      require(deriveType(m).get.t == natType)

      App(isZero, App(App(add, n), m))
    }.ensuring(deriveType(_).get.t == boolType)

    booleanEquivalent(suc(toChurch(0)), false)
    booleanEquivalent(suc(toChurch(10)), false)

    booleanEquivalent(ad(toChurch(0), toChurch(0)), true)
    booleanEquivalent(ad(toChurch(0), toChurch(1)), false)
    booleanEquivalent(ad(toChurch(1), toChurch(0)), false)
    booleanEquivalent(ad(toChurch(1), toChurch(2)), false)
  }

}