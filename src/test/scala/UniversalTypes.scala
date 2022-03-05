import stainless.lang.*
import stainless.collection.*

import verified.*
import SystemF.*
import Reduction.*
import Typing.*

import org.scalatest.*
import flatspec.*

// Tests to help ensure the implemented System F
// behaves (seemingly) correctly, so that we don't
// lose time trying to prove things which might not
// hold if the calculus is implemented incorrectly
class UniversalTypeTests extends AnyFlatSpec {
  
  val intType = BasicType("Int")

  "Type abstraction" should "yield universal type" in {
    val tabs = TAbs(Abs(VariableType(0), Var(0)))
    val td = deriveType(tabs).get

    assert(td.isValid)
    assert(td.t == UniversalType(ArrowType(VariableType(0), VariableType(0))))
  }

  it should "be typed correctly" in {
    val tabs: Term = TAbs(Abs(VariableType(0), Var(1)))
    val env: Environment = List(VariableType(0))

    val td = deriveType(env, tabs).get

    assert(td.t == UniversalType(ArrowType(VariableType(0), VariableType(1))))
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

  "Term substitution" should "behave correctly in case of TAbs" in {
    val t = TAbs(App(
      Abs(ArrowType(VariableType(0), VariableType(0)), TAbs(Var(0))), 
      Abs(VariableType(0), Var(0))
    ))

    val tp = TAbs(TAbs(Abs(VariableType(1), Var(0))))

    assert(reducesTo(t, tp).isDefined)

    val typ = UniversalType(UniversalType(ArrowType(VariableType(1), VariableType(1))))

    val td = deriveType(t).get
    val tdp = deriveType(tp).get
    assert(td.t == typ)
    assert(tdp.t == typ)
  }

}