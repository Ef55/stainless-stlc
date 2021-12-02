import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Typing {
  import STLC._

  sealed trait TypeDerivation {

    def env: Environment = this match {
      case VarDerivation(e, _, _) => e
      case AbsDerivation(e, _, _, _) => e
      case AppDerivation(e, _, _, _, _) => e
      case FixDerivation(e, _, _, _) => e
    }

    def t: Type = this match {
      case VarDerivation(_, t, _) => t
      case AbsDerivation(_, t, _, _) => t
      case AppDerivation(_, t, _, _, _) => t
      case FixDerivation(_, t, _, _) => t
    }

    def term: Term = this match{
      case VarDerivation(_, _, term) => term
      case AbsDerivation(_, _, term, _) => term
      case AppDerivation(_, _, term, _, _) => term
      case FixDerivation(_, _, term, _) => term
    }

    def isValid: Boolean = {
      this match{
        case VarDerivation(env, t, Var(k)) => {
          (k < env.size) && // Variable in environment
          env(k) == t       // and has the correct type
        }
        case AbsDerivation(env, ArrowType(typ1, typ2), Abs(typ, body), btd) => {
          btd.isValid && // Premise is valid,
          btd.term == body && btd.env == typ :: env && // and has matching attributes
          typ == typ1 && btd.t == typ2 // Types are correct
        }
        case AbsDerivation(_ ,_, _, _) => false // An abstraction should always have an arrow type...
        case AppDerivation(env, t, App(t1, t2), btd1, btd2) => {
          btd1.isValid && btd2.isValid && // Premises are valid
          btd1.term == t1 && btd2.term == t2 && btd1.env == env && btd2.env == env && // and have matching attributes
          btd1.t == ArrowType(btd2.t, t) // The body has expected type
        }
        case FixDerivation(env, t, Fix(f), ftd) => {
          ftd.isValid && // Premise is valid
          ftd.term == f && ftd.env == env && // and has matching attributes
          ftd.t == ArrowType(t, t) // Fixed term is a function
        }
      }
    }
    
  }
  case class VarDerivation(env: Environment, t: Type, term: Var) extends TypeDerivation
  case class AbsDerivation(env: Environment, t: Type, term: Abs, btd: TypeDerivation) extends TypeDerivation
  case class AppDerivation(env: Environment, t: Type, term: App, btd1: TypeDerivation, btd2: TypeDerivation) extends TypeDerivation
  case class FixDerivation(env: Environment, t: Type, term: Fix, ftd: TypeDerivation) extends TypeDerivation


  def deriveType(env: Environment, t: Term): Option[TypeDerivation] = {
    t match {
      case v@Var(k) => if (k < env.size) Some(VarDerivation(env, env(k), v)) else None()
      case abs@Abs(targ, body) => {
        val tb = deriveType(targ :: env, body)
        tb match {
          case None() => None()
          case Some(tb) => Some(AbsDerivation(env, ArrowType(targ, tb.t), abs, tb))
        }
      }
      case app@App(t1, t2) => {
        (deriveType(env, t1), deriveType(env, t2)) match {
          case (Some(ts1), Some(ts2)) => {
            ts1.t match{
              case ArrowType(targ, tres) if (targ == ts2.t) => 
                Some(AppDerivation(env, tres, app, ts1, ts2))
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
              case ArrowType(typ1, typ2) if typ1 == typ2 => Some(FixDerivation(env, typ1, fix, ftd))
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
  import STLCProperties._
  import ListProperties._

  // Type derivations

  @opaque @pure
  def deriveTypeCompleteness(@induct td: TypeDerivation): Unit = {
    require(td.isValid)
  }.ensuring(deriveType(td.env, td.term) == Some(td))

  @opaque @pure
  def deriveTypeValidity(env: Environment, t: Term): Unit = {
    t match {
      case Var(_) => ()
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
    case Some(td: TypeDerivation) => td.isValid && td.term == t && td.env == env
    case None() => true
  })

  @opaque @pure
  def TypeDerivationationsUniqueness(td1: TypeDerivation, td2: TypeDerivation): Unit = {
    require(td1.isValid)
    require(td2.isValid)
    require(td1.term == td2.term)
    require(td1.env == td2.env)

    deriveTypeCompleteness(td1)
    deriveTypeCompleteness(td2)
  }.ensuring(td1 == td2)

  @opaque @pure
  def TypeDerivationationTheorem(env: Environment, term: Term, td: TypeDerivation): Unit = {
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
  def typeOfCompleteness(@induct td: TypeDerivation): Unit ={
    require(td.isValid)
  }.ensuring(typeOf(td.env, td.term) == Some(td.t))

  // Progress

  @opaque @pure
  def callByValueProgress(t: Term): Unit = {
    require(deriveType(Nil(), t).isDefined)
    t match{
      case Var(_) => ()
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
      case Var(k) => {
        concatFirstIndexing(env, envExt, k)
      }
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
  def varEnvironmentStrengthening(v: Var, env: Environment, envExt: Environment): Unit = {
    require(typeOf(env ++ envExt, v).isDefined)
    require(v.k < env.length)
    concatFirstIndexing(env, envExt, v.k)
  }.ensuring(typeOf(env, v) == typeOf(env ++ envExt, v))

  @opaque @pure
  def varEnvironmentUpdate(v: Var, env: Environment, oldEnv: Environment, newEnv: Environment): Unit = {
    require(typeOf(env ++ oldEnv, v).isDefined)
    require(v.k < env.length)
    varEnvironmentStrengthening(v, env, oldEnv)
    environmentWeakening(v, env, newEnv)
  }.ensuring(typeOf(env ++ newEnv, v) == typeOf(env ++ oldEnv, v))

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
  def insertTypeInEnv(env1: Environment, typ: Type, env2: Environment, t: Term): Unit = {
    require(typeOf(env1 ++ env2, t).isDefined)

    t match{
      case Var(k) => {
        if (k < env1.size){
          varEnvironmentUpdate(Var(k), env1, env2, (typ :: env2))
          check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
        }
        else{
          insertionIndexing(env1, env2, typ, k)
          check(typeOf(env1 ++ env2, t) == typeOf(env1 ++ (typ :: env2), shift(t, 1, env1.size)))
        }
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
      case Var(k) => {
        if (k < env1.size) {
          varEnvironmentUpdate(Var(k), env1, typ :: env2, env2)
          check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
        }
        else {
          insertionIndexing(env1, env2, typ, k - 1)
          check(typeOf(env1 ++ (typ :: env2), t) == typeOf(env1 ++ env2, shift(t, -1, env1.size)))
        }
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
      case Var(_) => assert(typeOf(env, t) == typeOf(env, substitute(t, j, s)))
      case Abs(typ, body) => {
        insertTypeInEnv(Nil(), typ, env, s)
        preservationUnderSubst(typ :: env, body, j+1, shift(s, 1, 0))
      }
      case App(t1, t2) => {
        preservationUnderSubst(env, t1, j, s)
        preservationUnderSubst(env, t2, j, s)
      }
      case Fix(f) => {
        preservationUnderSubst(env, f, j, s)
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
      case Var(_) => ()
      case Abs(_, _) => ()
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