import stainless.lang._

import SystemF._
import Reduction._
import Typing._

import org.scalatest._
import flatspec._

class ChurchTests extends AnyFlatSpec {
  // This example requires two different natural types:
  // - Arithmetic NATural Type (anatType) -> allow to perform arithmetic operations
  // - Normalized NATural Type (nnatType) -> allow comparison of previously obtained naturals

  val baseType = BasicType("Base")
  val unitType = ArrowType(baseType, baseType)
  val boolType = ArrowType(unitType, ArrowType(unitType, unitType))

  def natType(natBase: Type): Type = {  
    ArrowType(ArrowType(natBase, natBase), ArrowType(natBase, natBase))
  }
  val nnatType = boolType
  val anatType = natType(nnatType)

  val unit = Abs(baseType, Var(0))
  val truw = Abs(unitType, Abs(unitType, Var(1)))
  val falz = Abs(unitType, Abs(unitType, Var(0)))
  def zero(natBase: Type): Term = {
     Abs(ArrowType(natBase, natBase), Abs(natBase, Var(0)))
  }.ensuring(res => deriveType(res).get.t == natType(natBase))

  def isZero(natBase: Type): Term = {
    require(natBase == nnatType)

    val nt = natType(natBase)
    Abs(nt, App(App(Var(0), Abs(boolType, falz)), truw))
  }

  def succ(natBase: Type): Term = {
    //require(natBase == nnatType)

    val nt = natType(natBase)
    // n -> 2; s -> 1; z -> 0
    Abs(nt, Abs(ArrowType(natBase, natBase), Abs(natBase, App(Var(1), App(App(Var(2), Var(1)), Var(0))))))
  }.ensuring(res => deriveType(res).get.t == ArrowType(natType(natBase), natType(natBase)))
  
  def generateAdder(natBase: Type): Term = {
    require(natBase == anatType)

    val nt = natType(natBase)
    // n -> 3; m -> 2; s -> 1; z -> 0
    Abs(nt, Abs(nt,
      Abs(ArrowType(natBase, natBase), Abs(natBase, 
        App(App(Var(3), Var(1)), App(App(Var(2), Var(1)), Var(0)))
      ))
    ))
  }.ensuring(res => deriveType(res).get.t == ArrowType(natType(natBase), ArrowType(natType(natBase), natType(natBase))))

  // def mult(natBase: Type): Term = {
  //   val nt = natType(natBase)
  //   val multiplier = 
  //     // rec -> 4; n -> 3; m -> 2; s -> 1; z -> 0
  //     Abs(ArrowType(nt, ArrowType(nt, nt)), 
  //       Abs(nt, Abs(nt, 
  //         Abs(ArrowType(natBase, natBase), Abs(natBase), 

  //         )
  //       ))
  //     )
  // }

  def number(k: Int, natBase: Type): Term = {
    require(k >= 0)
    Abs(ArrowType(natBase, natBase), Abs(natBase, 
      if(k == 0) Var(0) else App(Var(1), App(App(number(k-1, natBase), Var(1)), Var(0)))
    ))
  }.ensuring(res => deriveType(res).get.t == natType(natBase))

  def normalizeNumber(t: Term): Term = {
    require(deriveType(t).get.t == natType(anatType))

    val s = succ(nnatType)
    val z = zero(nnatType)
    assert(deriveType(s).get.t == ArrowType(natType(nnatType), natType(nnatType)))
    assert(deriveType(z).get.t == natType(nnatType))

    val computation = App(App(t, s), z)
    assert(deriveType(computation).get.t == natType(nnatType))

    reduce(computation)
  }

  def ite(thenn: Term, elze: Term): Term = {
    require(deriveType(thenn).get.t == unitType)
    require(deriveType(elze).get.t == unitType)

    Abs(boolType, App(App(Var(0), 
      Abs(unitType, thenn)),
      Abs(unitType, elze))
    )
  }

  def reduceN(t: Term, fuel: BigInt): Term = {
    if(fuel == 0) {
      t
    }
    else {
      reduceCallByValue(t) match {
        case Some(tp) => reduceN(tp, fuel-1)
        case _ => t
      }
    }
  }

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

  "Constants" should "have expected type" in {
    def isValueWithType(t: Term, typ: Type): Unit = {
      assert(t.isValue)
      assert(deriveType(t).get.t == typ)
      assert(reduceCallByValue(t).isEmpty)
    }

    isValueWithType(unit, unitType)
    isValueWithType(truw, boolType)
    isValueWithType(falz, boolType)
  }

  "Boolean operations" should "have expected behavior" in {
    def testIsZero(n: Int): Unit = {
      val t = reduce(App(isZero(nnatType), number(n, nnatType)))
      if(n == 0) {
        assert(t == truw)
      }
      else {
        assert(t == falz)
      }
    }

    testIsZero(0)
    testIsZero(1)
    testIsZero(10)
  }

  "Number operations" should "yield correct result" in {
    def testNumber(at: Term, n: Int): Unit = {
      val t = normalizeNumber(reduce(at))
      assert(t == number(n, nnatType))

      for(
        i <- 0 until n*n
        if i != n
      ){
        assert(t != number(i, nnatType))
      }
    }

    def testSucc(n: Int): Unit = {
      testNumber(App(succ(anatType), number(n, anatType)), n+1)
    }

    def add(n: Term, m: Term): Term = {
      require(deriveType(n).get.t == natType(anatType))
      require(deriveType(m).get.t == natType(anatType))
      App(App(generateAdder(anatType), n), m)
    }

    def testAddition(n: Int, ns: Int*): Unit = {
      val addition = ns.foldLeft(number(n, anatType))((n, m) => add(n, number(m, anatType)))
      testNumber(addition, ns.foldLeft(n)(_ + _))
    }

    testSucc(0)
    testSucc(1)
    testSucc(10)

    testAddition(0, 0)
    testAddition(0, 1)
    testAddition(1, 0)
    testAddition(1, 1)
    testAddition(2, 3)
    testAddition(7, 5)
    testAddition(1, 2, 3)
    testAddition(1, 0, 5, 1)
    // testAddition(10, 10) // > 2min...
  }

  // def sumOfIntegers: Unit = {
  //   def run(n: BigInt): (Term, Term) = {

  //     (Var(0), Var(0))

  //   }.ensuring(res => res._1 == res._2)
  // }

}