import stainless.lang._

import SystemF._
import Reduction._
import Typing._

import org.scalatest._
import flatspec._

class UniversalTypeTests extends AnyFlatSpec {
  
  val intType = BasicType("Int")

  "Type abstraction" should "yield universal type" in {
    val tabs = TAbs(Abs(VariableType(0), Var(0)))
    val td = deriveType(tabs).get

    assert(td.isValid)
    assert(td.t == UniversalType(ArrowType(VariableType(0), VariableType(0))))
  }

  "Type application" should "replace universal type" in {
    val tapp = TApp(TAbs(Abs(VariableType(0), Var(0))), intType)
    val td = deriveType(tapp).get

    assert(td.isValid)
    assert(td.t == ArrowType(intType, intType))
  }

  it should "lead to substitution in single step" in {
    val tapp = TApp(TAbs(Abs(VariableType(0), Var(0))), intType)
    val red = reduceCallByValue(tapp).get
    val td = deriveType(red).get

    assert(td.isValid)
    assert(td === deriveType(tapp).get)
    assert(td.t == ArrowType(intType, intType))
    assert(red == Abs(intType, Var(0)))
  }

  it should "not break in case of nested type abstractions" in {
    val fun = TAbs(Abs(VariableType(0), TAbs(Abs(intType, Var(1)))))
    val funTd = deriveType(fun).get

    assert(funTd.isValid)
    assert(funTd.t == UniversalType(ArrowType(VariableType(0), UniversalType(ArrowType(intType, VariableType(1))))))

    val app = TApp(fun, intType)
    val appTd = deriveType(app).get

    assert(appTd.isValid)
    assert(appTd.t == ArrowType(intType, UniversalType(ArrowType(intType, intType))))

    val red = reduceCallByValue(app).get
    val redTd = deriveType(red).get
    
    assert(redTd.isValid)
    assert(redTd.t == ArrowType(intType, UniversalType(ArrowType(intType, intType))))
}

}