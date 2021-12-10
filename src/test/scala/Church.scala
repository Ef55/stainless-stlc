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

  val unit: Term = TAbs(Abs(VariableType(0), Var(0)))
  val truw: Term = TAbs(Abs(VariableType(0), Abs(VariableType(0), Var(1))))
  val falz: Term = TAbs(Abs(VariableType(0), Abs(VariableType(0), Var(0))))
  val zero: Term = TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), Var(0))))

  val succ: Term = Abs(natType, TAbs(Abs(ArrowType(VariableType(0), VariableType(0)), Abs(VariableType(0), 
    App(Var(1), App(App(TApp(Var(2), VariableType(0)), Var(1)), Var(0)))
  ))))
  val isZero: Term = Abs(natType, TAbs(
    App(App(TApp(Var(0), 
      boolType.t), 
      Abs(boolType.t, TApp(falz, VariableType(0)))), 
      TApp(truw, VariableType(0)))
  ))

  val add: Term = Abs(natType, Abs(natType,
    App(App(TApp(Var(1), natType), succ), Var(0))
  ))
  val mult: Term = Abs(natType, Abs(natType,
    App(App(TApp(Var(1), natType), App(add, Var(0))), zero)
  ))

  val pred: Term = ({ 
    val natPairType = ArrowType(boolType, natType)
    val mkPair = Abs(natType, Abs(natType, Abs(boolType, 
      App(App(TApp(Var(0), natType), Var(2)), Var(1))
    )))
    val predStep = Abs(natPairType, 
      App(App(mkPair, 
        App(succ, App(Var(0), truw))), 
        App(Var(0), truw)
      )
    )

    Abs(natType, App( App(App(TApp(Var(0), natPairType), predStep), App(App(mkPair, zero), zero)) , falz))
  })

  val fact: Term = reduce(Fix(Abs(ArrowType(natType, natType), Abs(natType,
    App(App(App(TApp(App(isZero, Var(0)), ArrowType(unitType, natType)), 
      Abs(unitType, App(succ, zero))), 
      Abs(unitType, App(App(mult, Var(1)), App(Var(2), App(pred, Var(1)))))
    ), unit)
  ))))
 
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

  def natEquivalent(t: Term, s: Term): Unit = {
    require(deriveType(t).get.t == natType)
    require(deriveType(s).get.t == natType)

    assert( reduce(App(App(TApp(t, natType), succ), zero)) == reduce(App(App(TApp(s, natType), succ), zero)) )
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
    isValueWithType(mult, ArrowType(natType, ArrowType(natType, natType)))
    isValueWithType(isZero, ArrowType(natType, boolType))
    isValueWithType(pred, ArrowType(natType, natType))
    isValueWithType(fact, ArrowType(natType, natType))
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

  "Mult" should "return the expected natural" in {
    def apply(n: Term, m: Term): Term = {
      require(deriveType(n).get.t == natType)
      require(deriveType(m).get.t == natType)

      App(App(mult, n), m)
    }

    def test(n: Int, ns: Int*): Unit = {
      val multiplication = ns.foldLeft(toChurch(n))((n, m) => apply(n, toChurch(m)))
      val prod = ns.foldLeft(n)(_ * _)

      natEquivalent(multiplication, prod)
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

  it should "compose correctly with Succ and Add" in {
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

  "Pred" should "return the expected natural" in {
    def apply(n: Term): Term = {
      require(deriveType(n).get.t == natType)

      App(pred, n)
    }.ensuring(deriveType(_).get.t == natType)


    natEquivalent(apply(zero), 0)
    natEquivalent(apply(toChurch(1)), 0)
    natEquivalent(apply(toChurch(10)), 9)
  }

  "Fact" should "return the expected natural" in {
    def test(n: Int, fn: Int): Unit = {
      natEquivalent( reduce(App(fact, toChurch(n))), fn )
    }

    test(0, 1)
    test(1, 1)
    test(3, 6)
    // test(4, 24) // ~10s
  }

  "Gauss' story" should "be System F compatible" in {
    def sum(ns: List[Int]): Term = {
      def apply(n: Term, m: Term): Term = {
        App(App(add, n), m)
      }

      ns.foldLeft(zero)((n, m) => apply(n, toChurch(m)))
    }

    def instance(n: Int): Unit = {
      val s = sum( (1 to n).toList )
      val ds = App(App(add, s), s)

      val f = App(App(mult, toChurch(n)), App(succ, toChurch(n)))

      natEquivalent(ds, f)
    }

    instance(3)
  }

}