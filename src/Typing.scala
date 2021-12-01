import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Typing {
  import STLC._

  sealed trait TypeDeriv {

    def env: Environment = this match {
      case VarDeriv(e, _, _) => e
      case CstDeriv(e, _, _) => e
      case AbsDeriv(e, _, _, _) => e
      case AppDeriv(e, _, _, _, _) => e
      case FixDeriv(e, _, _, _) => e
    }

    def t: Type = this match {
      case VarDeriv(_, t, _) => t
      case CstDeriv(_, t, _) => t
      case AbsDeriv(_, t, _, _) => t
      case AppDeriv(_, t, _, _, _) => t
      case FixDeriv(_, t, _, _) => t
    }

    def term: Term = this match{
      case VarDeriv(_, _, term) => term
      case CstDeriv(_, _, term) => term
      case AbsDeriv(_, _, term, _) => term
      case AppDeriv(_, _, term, _, _) => term
      case FixDeriv(_, _, term, _) => term
    }

    def isValid: Boolean = {
      this match{
        case VarDeriv(env, t, va) => if (va.k < env.size) env(va.k) == t else false
        case CstDeriv(env, t, Cst(cst)) => Constants.typeOf(cst) == t
        case AbsDeriv(env, t, abs, btd) => btd.term == abs.t && btd.isValid && btd.env == abs.b :: env && (t match{
          case BaseType(_) => false
          case ArrowType(t1, t2) => abs.b == t1 && btd.t == t2
        })
        case AppDeriv(env, t, app, btd1, btd2) => btd1.term == app.t1 && btd2.term == app.t2 && btd1.env == env && btd2.env == env && btd1.t == ArrowType(btd2.t, t) && btd1.isValid && btd2.isValid
        case FixDeriv(env, t, Fix(f), ftd) => ftd.term == f && ftd.env == env && ftd.t == ArrowType(t, t) && ftd.isValid
      }
    }
    
  }
  case class VarDeriv(env: Environment, t: Type, term: Variable) extends TypeDeriv
  case class CstDeriv(env: Environment, t: Type, term: Cst) extends TypeDeriv
  case class AbsDeriv(env: Environment, t: Type, term: Abs, btd: TypeDeriv) extends TypeDeriv
  case class AppDeriv(env: Environment, t: Type, term: App, btd1: TypeDeriv, btd2: TypeDeriv) extends TypeDeriv
  case class FixDeriv(env: Environment, t: Type, term: Fix, ftd: TypeDeriv) extends TypeDeriv


  def deriveType(env: Environment, t: Term): Option[TypeDeriv] = {
    t match {
      case v@Variable(k) => if (k < env.size) Some(VarDeriv(env, env(k), v)) else None()
      case c@Cst(cst) => Some(CstDeriv(env, Constants.typeOf(cst), c))
      case abs@Abs(targ, body) => {
        val tb = deriveType(targ :: env, body)
        tb match {
          case None() => None()
          case Some(tb) => Some(AbsDeriv(env, ArrowType(targ, tb.t), abs, tb))
        }
      }
      case app@App(t1, t2) => {
        (deriveType(env, t1), deriveType(env, t2)) match {
          case (Some(ts1), Some(ts2)) => {
            ts1.t match{
              case ArrowType(targ, tres) if (targ == ts2.t) => 
                Some(AppDeriv(env, tres, app, ts1, ts2))
              case _ => None()
            }
          }
          case (_, _) => None()
        }
      }
      case fix@Fix(f) => {
        deriveType(env, f) match {
          case Some(ftd) => {
            ftd.t match {
              case ArrowType(typ1, typ2) if typ1 == typ2 => Some(FixDeriv(env, typ1, fix, ftd))
              case _ => None()
            }
          }
          case _ => None()
        }
      }
    }
  }
  
  def typeOf(env: Environment, t: Term): Option[Type] = {
    deriveType(env, t).map(der => der.t)
  }

  def typeOf(t: Term): Option[Type] = {
    typeOf(Nil(), t)
  }
}

object TypingProperties {
  import STLC._
  import Typing._
  import Reduction._
  import ListProperties._
  import TermsProperties._

  // Type derivations

  @opaque @pure
  def deriveTypeCompleteness(@induct td: TypeDeriv): Unit = {
    require(td.isValid)
  }.ensuring(deriveType(td.env, td.term) == Some(td))

  @opaque @pure
  def deriveTypeValidity(env: Environment, t: Term): Unit = {
    t match {
      case Variable(_) => ()
      case Cst(_) => ()
      case Abs(targ, body) => {
        deriveTypeValidity(targ :: env, body)
      }
      case App(t1, t2) => {
        deriveTypeValidity(env, t1)
        deriveTypeValidity(env, t2)
      }
      case Fix(f) => {
        deriveTypeValidity(env, f)
      }
    }
  }.ensuring(deriveType(env, t) match {
    case Some(td: TypeDeriv) => td.isValid && td.term == t && td.env == env
    case None() => true
  })

  @opaque @pure
  def typeDerivationsUniqueness(td1: TypeDeriv, td2: TypeDeriv): Unit = {
    require(td1.isValid)
    require(td2.isValid)
    require(td1.term == td2.term)
    require(td1.env == td2.env)

    deriveTypeCompleteness(td1)
    deriveTypeCompleteness(td2)
  }.ensuring(td1 == td2)

  @opaque @pure
  def typeDerivationTheorem(env: Environment, term: Term, td: TypeDeriv): Unit = {
    deriveTypeValidity(env, term)
    if(td.isValid) {
      deriveTypeCompleteness(td)
    }
    else {
      assert(deriveType(env, term) != Some(td))
    }
  }.ensuring(
    (deriveType(env, term) == Some(td))
    ==
    (td.isValid && td.env == env && td.term == term)
  )
  
  // TypeOf

  @opaque @pure
  def typeOfCompleteness(@induct td: TypeDeriv): Unit ={
    require(td.isValid)
  }.ensuring(typeOf(td.env, td.term) == Some(td.t))


  // Progress

  @opaque @pure
  def callByValueProgress(t: Term): Unit = {
    require(deriveType(Nil(), t).isDefined)
    t match{
      case Variable(_) => ()
      case Cst(_) => ()
      case Abs(_, _) => ()
      case App(t1, t2) => {
        callByValueProgress(t1)
        callByValueProgress(t2) 
      }
      case Fix(f) => callByValueProgress(f)
    }
  }.ensuring(reduceCallByValue(t).isDefined || t.isValue)

  // Preservation

  @opaque @pure
  def environmentWeakening(t: Term, env: Environment, envExt: Environment): Unit = {
    require(typeOf(env, t).isDefined)

    t match{
      case Variable(k) => {
        concatFirstIndexing(env, envExt, k)
      }
      case Cst(_) => ()
      case Abs(targ, body) => {
        environmentWeakening(body, targ :: env, envExt)
      }
      case App(t1, t2) => {
        environmentWeakening(t1, env, envExt)
        environmentWeakening(t2, env, envExt)
      }
      case Fix(f) => {
        environmentWeakening(f, env, envExt)
      }
    }
  }.ensuring(typeOf(env, t) == typeOf(env ++ envExt, t))

  @opaque @pure
  def variableEnvironmentStrengthening(v: Variable, env: Environment, envExt: Environment): Unit = {
    require(typeOf(env ++ envExt, v).isDefined)
    require(v.k < env.length)
    concatFirstIndexing(env, envExt, v.k)
  }.ensuring(typeOf(env, v) == typeOf(env ++ envExt, v))

  @opaque @pure
  def variableEnvironmentUpdate(v: Variable, env: Environment, oldEnv: Environment, newEnv: Environment): Unit = {
    require(typeOf(env ++ oldEnv, v).isDefined)
    require(v.k < env.length)
    variableEnvironmentStrengthening(v, env, oldEnv)
    environmentWeakening(v, env, newEnv)
  }.ensuring(typeOf(env ++ newEnv, v) == typeOf(env ++ oldEnv, v))

  @opaque @pure
  def absInversionLemma(env: Environment, targ: Type, body: Term): Unit = {
    require(typeOf(targ :: env, body).isDefined)
  }.ensuring(
    typeOf(env, Abs(targ, body)).get
    == 
    ArrowType(targ, typeOf(targ:: env, body).get)
  )

  @opaque @pure
  def appInversionLemma(env: Environment, t1: Term, t2: Term): Unit = {
    require(typeOf(env, App(t1, t2)).isDefined)

    assert(typeOf(env, t1).isDefined)
    assert(typeOf(env, t2).isDefined)

  }.ensuring(
    typeOf(env, t1).get 
    == 
    ArrowType(typeOf(env, t2).get, typeOf(env, App(t1, t2)).get)
  )

  @opaque @pure
  def cstEnvironmentInvariance(env1: Environment, env2: Environment, cst: Term): Unit = {
    require(cst.isInstanceOf[Cst])
    assert(typeOf(env1, cst).isDefined)
    assert(typeOf(env2, cst).isDefined)
  }.ensuring(
    typeOf(env1, cst).get
    ==
    typeOf(env2, cst).get
  )

  @opaque @pure
  def insertTypeInEnv(env1: Environment, typ: Type, env2: Environment, t: Term): Unit = {
    require(typeOf(env1 ++ env2, t).isDefined)

    t match{
      case Variable(k) => {
        if (k < env1.size){
          variableEnvironmentUpdate(Variable(k), env1, env2, (typ :: env2))
          check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
        }
        else{
          insertionIndexing(env1, env2, typ, k)
          check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
        }
      }
      case Cst(_) => {
        cstEnvironmentInvariance(env1 ++ env2, env1 ++ (typ :: env2), t)
        check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
      }
      case Abs(targ, body) => {
        absInversionLemma(env1 ++ env2, targ, body)
        insertTypeInEnv(targ :: env1, typ, env2, body)
        absInversionLemma(env1 ++ (typ :: env2), targ, shift(body, 1, env1.size + 1))
        check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
      }
      case App(t1, t2) => {
        appInversionLemma(env1 ++ env2, t1, t2)
        insertTypeInEnv(env1, typ, env2, t2)
        insertTypeInEnv(env1, typ, env2, t1)
        appInversionLemma(env1 ++ (typ :: env2), shift(t1, 1, env1.size), shift(t2, 1, env1.size))
        check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
      }
      case Fix(f) => {
        insertTypeInEnv(env1, typ, env2, f)
        check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
      }
    }

    assert(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
    OptionProperties.equalityImpliesDefined(
      typeOf(env1 ++ env2, t),
      typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)), 
    )
  }.ensuring(
    typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)).isDefined 
    &&
    ( typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)) )
  )

  @opaque @pure
  def removeTypeInEnv(env1: Environment, typ: Type, env2: Environment, t: Term): Unit = {
    require(typeOf(env1 ++ (typ :: env2), t).isDefined)
    require(!t.hasFreeVariablesIn(env1.size, 1))

    ReductionProperties.boundRangeShiftBackLemma(t, 1, env1.size)
    t match {
      case Variable(k) => {
        if (k < env1.size) {
          variableEnvironmentUpdate(Variable(k), env1, typ :: env2, env2)
          check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
        }
        else {
          insertionIndexing(env1, env2, typ, k - 1)
          check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
        }
      }
      case Cst(_) => {
        cstEnvironmentInvariance(env1 ++ env2, env1 ++ (typ :: env2), t)
        check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
      }
      case Abs(targ, body) => {
        absInversionLemma(env1 ++ (typ :: env2), targ, body)
        removeTypeInEnv(targ :: env1, typ, env2, body)
        absInversionLemma(env1 ++ env2, targ, shift(body, -1, env1.size + 1))
        check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
      }
      case App(t1, t2) => {
        appInversionLemma(env1 ++ (typ :: env2), t1, t2)
        removeTypeInEnv(env1, typ, env2, t2)
        removeTypeInEnv(env1, typ, env2, t1)
        appInversionLemma(env1 ++ env2, shift(t1, -1, env1.size), shift(t2, -1, env1.size))
        assert(App(shift(t1, -1, env1.size), shift(t2, -1, env1.size)) == shift(t, -1, env1.size))
        check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
      }
      case Fix(f) => {
        removeTypeInEnv(env1, typ, env2, f)
        check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
      }
    }

    assert(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
    OptionProperties.equalityImpliesDefined(
      typeOf(env1 ++ (typ :: env2), t), 
      typeOf(env1 ++ env2, shift(t, -1, env1.size))
    )
  }.ensuring(
    typeOf(env1 ++ env2, shift(t, -1, env1.size)).isDefined 
    &&
    ( typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)) )
  )

  @opaque @pure
  def preservationUnderSubst(env: Environment, t: Term, j: BigInt, s: Term): Unit = {
    require(typeOf(env, t).isDefined)
    require(typeOf(env, s).isDefined)
    require(0 <= j && j < env.size)
    require(env(j) == typeOf(env, s).get)

    t match {
      case Variable(_) => assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      case Cst(_) => assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      case Abs(typ, body) => {
        insertTypeInEnv(Nil(), typ, env, s)
        preservationUnderSubst(typ :: env, body, j+1, shift(s, 1, 0))
        assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      }
      case App(t1, t2) => {
        preservationUnderSubst(env, t1, j, s)
        preservationUnderSubst(env, t2, j, s)
        assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      }
      case Fix(f) => {
        preservationUnderSubst(env, f, j, s)
        assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      }
    }
  }.ensuring(typeOf(env, t) == typeOf(env, substitute(t, j, s)))

  @opaque @pure
  def preservationUnderAbsSubst(env: Environment, body: Term, arg: Term) = {
    require(typeOf(env, arg).isDefined)
    require(typeOf(typeOf(env, arg).get :: env, body).isDefined)

    
    val Some(argType) = typeOf(env, arg)
    val Some(typ) = typeOf(argType :: env, body)

    insertTypeInEnv(Nil(), argType, env, arg)
    assert(typeOf(argType :: env, shift(arg, 1, 0)).get == argType)
    preservationUnderSubst(argType :: env, body, 0, shift(arg, 1, 0))

    assert(!arg.hasFreeVariablesIn(0, 0))
    ReductionProperties.boundRangeShift(arg, 1, 0, 0)
    ReductionProperties.boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    ReductionProperties.boundRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    removeTypeInEnv(Nil(), argType, env, substitute(body, 0, shift(arg, 1, 0)))

  }.ensuring(typeOf(env, absSubsitution(body, arg)) == typeOf(typeOf(env, arg).get :: env, body))
  
  @opaque @pure
  def callByValuePreservationTheorem(env: Environment, t: Term): Unit = {
    require(typeOf(env, t).isDefined)
    require(reduceCallByValue(t).isDefined)
    val typeT = typeOf(env, t).get

    t match{
      case App(t1, t2) => {
        if(!t1.isValue) {
          callByValuePreservationTheorem(env, t1)
        }
        else if(!t2.isValue)
          callByValuePreservationTheorem(env, t2)
        else {
          assert(t1.isValue && t2.isValue)
          t1 match {
              case Abs(_, body) => 
                preservationUnderAbsSubst(env, body, t2)
              case _ => ()
          }
        }
      }
      case Fix(f) => {
        if(!f.isValue) {
          callByValuePreservationTheorem(env, f)
        }
        else {
          f match {
            case Abs(_, body) => preservationUnderAbsSubst(env, body, t)
          }
        }
      }
    }
  }.ensuring( typeOf(env, reduceCallByValue(t).get) == typeOf(env, t) )

}