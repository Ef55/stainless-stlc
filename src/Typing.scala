import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Typing {
  import SystemF._
  import Reduction._

  type Environment = List[Type]

  sealed trait TypeDerivation {

    def env: Environment = this match {
      case VarDerivation(e, _, _) => e
      case AbsDerivation(e, _, _, _) => e
      case AppDerivation(e, _, _, _, _) => e
      case FixDerivation(e, _, _, _) => e
      case TAbsDerivation(e, _, _, _) => e
      case TAppDerivation(e, _, _, _) => e
    }

    def t: Type = this match {
      case VarDerivation(_, t, _) => t
      case AbsDerivation(_, t, _, _) => t
      case AppDerivation(_, t, _, _, _) => t
      case FixDerivation(_, t, _, _) => t
      case TAbsDerivation(_, t, _, _) => t
      case TAppDerivation(_, t, _, _) => t
    }

    def term: Term = this match{
      case VarDerivation(_, _, term) => term
      case AbsDerivation(_, _, term, _) => term
      case AppDerivation(_, _, term, _, _) => term
      case FixDerivation(_, _, term, _) => term
      case TAbsDerivation(_, _, term, _) => term
      case TAppDerivation(_, _, term, _) => term
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
        case TAbsDerivation(env, UniversalType(b), tabs, btd) => {
          btd.isValid &&
          btd.term == tabs.t && btd.env == env &&
          btd.t == b
        }
        case TAbsDerivation(_ ,_, _, _) => false
        case TAppDerivation(env, t, tapp, btd) => {
          btd.term == tapp.t && 
          btd.isValid && 
          btd.env == env && 
          (btd.t match{
            case UniversalType(b) => t == universalSubstitution(b, tapp.typ)
            case _ => false
          })
        }
      }
    }
    
    def ===(that: TypeDerivation): Boolean = {
      this.t == that.t
    }
  }
  case class VarDerivation(env: Environment, t: Type, term: Var) extends TypeDerivation
  case class AbsDerivation(env: Environment, t: Type, term: Abs, btd: TypeDerivation) extends TypeDerivation
  case class AppDerivation(env: Environment, t: Type, term: App, btd1: TypeDerivation, btd2: TypeDerivation) extends TypeDerivation
  case class FixDerivation(env: Environment, t: Type, term: Fix, ftd: TypeDerivation) extends TypeDerivation
  case class TAbsDerivation(env: Environment, t: Type, term: TAbs, btd: TypeDerivation) extends TypeDerivation
  case class TAppDerivation(env: Environment, t: Type, term: TApp, btd: TypeDerivation) extends TypeDerivation


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
      case tabs@TAbs(t) => {
        deriveType(env, t) match{
          case Some(btd) => Some(TAbsDerivation(env, UniversalType(btd.t), tabs, btd))
          case None() => None()
        }
      }

      case tapp@TApp(t, typ) => {
        deriveType(env, t) match{
          case Some(btd) => {
            btd.t match{
              case UniversalType(b) => Some(TAppDerivation(env, universalSubstitution(b, typ), tapp, btd))
              case _ => None()
            }
            
          }
          case None() => None()
        }
      }
    }
  }
  
  // def typeOf(env: Environment, t: Term): Option[Type] = {
  //   deriveType(env, t).map(der => der.t)
  // }

  // def typeOf(t: Term): Option[Type] = {
  //   typeOf(Nil(), t)
  // }
 }

object TypingProperties {
  import SystemF._
  import Typing._
  import Reduction._  
  import Transformations.{ Terms => TermTr, Types => TypeTr }

  import ListProperties._
  import SystemFProperties.{ Terms => TermProp, Types => TypeProp }
  import TransformationsProperties.{ Terms => TermTrProp, Types => TypeTrProp }

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
      case TAbs(t) => {
        deriveTypeValidity(env, t)
      }
      case TApp(t, typ) => {
        deriveTypeValidity(env, t)
      }
    }
  }.ensuring(deriveType(env, t) match {
    case Some(td: TypeDerivation) => td.isValid && td.term == t && td.env == env
    case None() => true
  })

  @opaque @pure
  def typeDerivationsUniqueness(td1: TypeDerivation, td2: TypeDerivation): Unit = {
    require(td1.isValid)
    require(td2.isValid)
    require(td1.term == td2.term)
    require(td1.env == td2.env)

    deriveTypeCompleteness(td1)
    deriveTypeCompleteness(td2)
  }.ensuring(td1 == td2)

  @opaque @pure
  def typeDerivationTheorem(env: Environment, term: Term, td: TypeDerivation): Unit = {
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
  // @opaque @pure
  // def typeOfCompleteness(td: TypeDerivation): Unit ={
  //   require(td.isValid)
  //   deriveTypeCompleteness(td)
  // }.ensuring(typeOf(td.env, td.term) == Some(td.t))


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
      case TAbs(t) => ()
      case TApp(t, typ) => callByValueProgress(t)
    }
  }.ensuring(reduceCallByValue(t).isDefined || t.isValue)

  // Preservation

  @opaque @pure
  def environmentWeakening(t: Term, env: Environment, envExt: Environment): Unit = {
    require(deriveType(env, t).isDefined)

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
      case TAbs(t) => {
        environmentWeakening(t, env, envExt)
      }
      case TApp(t, typ) => {
        environmentWeakening(t, env, envExt)
      }
    }
  }.ensuring(
    deriveType(env ++ envExt, t).isDefined &&
    (deriveType(env, t).get === deriveType(env ++ envExt, t).get)
  )

  @opaque @pure
  def variableEnvironmentStrengthening(v: Var, env: Environment, envExt: Environment): Unit = {
    require(deriveType(env ++ envExt, v).isDefined)
    require(v.k < env.length)
    concatFirstIndexing(env, envExt, v.k)
  }.ensuring(deriveType(env, v).get === deriveType(env ++ envExt, v).get)

  @opaque @pure
  def variableEnvironmentUpdate(v: Var, env: Environment, oldEnv: Environment, newEnv: Environment): Unit = {
    require(deriveType(env ++ oldEnv, v).isDefined)
    require(v.k < env.length)
    variableEnvironmentStrengthening(v, env, oldEnv)
    environmentWeakening(v, env, newEnv)
  }.ensuring(deriveType(env ++ newEnv, v).get === deriveType(env ++ oldEnv, v).get)

  @opaque @pure
  def absInversionLemma(env: Environment, targ: Type, body: Term): Unit = {
    require(deriveType(targ :: env, body).isDefined)
  }.ensuring(
    deriveType(env, Abs(targ, body)).get.t
    == 
    ArrowType(targ, deriveType(targ:: env, body).get.t)
  )

  @opaque @pure
  def appInversionLemma(env: Environment, t1: Term, t2: Term): Unit = {
    require(deriveType(env, App(t1, t2)).isDefined)

    assert(deriveType(env, t1).isDefined)
    assert(deriveType(env, t2).isDefined)

  }.ensuring(
    deriveType(env, t1).get.t 
    == 
    ArrowType(deriveType(env, t2).get.t, deriveType(env, App(t1, t2)).get.t)
  )

  @opaque @pure
  def fixInversionLemma(env: Environment, f: Term): Unit = {
    require(deriveType(env, Fix(f)).isDefined)

    assert(deriveType(env, f).isDefined)
    assert(deriveType(env, f).get.t match {
      case ArrowType(t1, t2) => t1 == t2
      case _ => false
    })
  }.ensuring(
    deriveType(env, f).get.t
    ==
    ArrowType(deriveType(env, Fix(f)).get.t, deriveType(env, Fix(f)).get.t)
  )

  @opaque @pure
  def tabsInversionLemma(env: Environment, body: Term): Unit = {
    require(deriveType(env, TAbs(body)).isDefined)
  }.ensuring(
    UniversalType(deriveType(env, body).get.t)
    ==
    deriveType(env, TAbs(body)).get.t
  )

  @opaque @pure
  def tappInversionLemma(env: Environment, abs: Term, typ: Type): Unit = {
    require(deriveType(env, TApp(abs, typ)).isDefined)
  }.ensuring(
    deriveType(env, abs).get.t match {
      case UniversalType(t) => universalSubstitution(t, typ) == deriveType(env, TApp(abs, typ)).get.t
    }
  )

  @opaque @pure
  def insertTypeInEnv(env1: Environment, typ: Type, env2: Environment, t: Term): Unit = {
    require(deriveType(env1 ++ env2, t).isDefined)

    t match{
      case Var(k) => {
        if (k < env1.size){
          variableEnvironmentUpdate(Var(k), env1, env2, (typ :: env2))
          check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
        }
        else{
          insertionIndexing(env1, env2, typ, k)
          check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
        }
      }
      case Abs(targ, body) => {
        absInversionLemma(env1 ++ env2, targ, body)
        insertTypeInEnv(targ :: env1, typ, env2, body)
        absInversionLemma(env1 ++ (typ :: env2), targ, TermTr.shift(body, 1, env1.size + 1))
        check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
      }
      case App(t1, t2) => {
        appInversionLemma(env1 ++ env2, t1, t2)
        insertTypeInEnv(env1, typ, env2, t2)
        insertTypeInEnv(env1, typ, env2, t1)
        appInversionLemma(env1 ++ (typ :: env2), TermTr.shift(t1, 1, env1.size), TermTr.shift(t2, 1, env1.size))
        check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
      }
      case Fix(f) => {
        insertTypeInEnv(env1, typ, env2, f)
        check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
      }
      case TAbs(body) => {
        insertTypeInEnv(env1, typ, env2, body)
        check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
      }
      case TApp(body, _) => {
        insertTypeInEnv(env1, typ, env2, body)
        check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
      }
    }

    // assert(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    // OptionProperties.equalityImpliesDefined(
    //   typeOf(env1 ++ env2, t),
    //   typeOf(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)), 
    // )
  }.ensuring(
    deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).isDefined 
    &&
    ( deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get )
  )

  @opaque @pure
  def removeTypeInEnv(env1: Environment, typ: Type, env2: Environment, t: Term): Unit = {
    require(deriveType(env1 ++ (typ :: env2), t).isDefined)
    require(!t.hasFreeVariablesIn(env1.size, 1))

    TermTrProp.boundRangeShiftBackLemma(t, 1, env1.size)
    t match {
      case Var(k) => {
        if (k < env1.size) {
          variableEnvironmentUpdate(Var(k), env1, typ :: env2, env2)
          check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
        }
        else {
          insertionIndexing(env1, env2, typ, k - 1)
          check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
        }
      }
      case Abs(targ, body) => {
        absInversionLemma(env1 ++ (typ :: env2), targ, body)
        removeTypeInEnv(targ :: env1, typ, env2, body)
        absInversionLemma(env1 ++ env2, targ, TermTr.shift(body, -1, env1.size + 1))
        check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
      }
      case App(t1, t2) => {
        appInversionLemma(env1 ++ (typ :: env2), t1, t2)
        removeTypeInEnv(env1, typ, env2, t2)
        removeTypeInEnv(env1, typ, env2, t1)
        appInversionLemma(env1 ++ env2, TermTr.shift(t1, -1, env1.size), TermTr.shift(t2, -1, env1.size))
        assert(App(TermTr.shift(t1, -1, env1.size), TermTr.shift(t2, -1, env1.size)) == TermTr.shift(t, -1, env1.size))
        check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
      }
      case Fix(f) => {
        removeTypeInEnv(env1, typ, env2, f)
        fixInversionLemma(env1 ++ env2, TermTr.shift(f, -1, env1.size))
        check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
      }
      case TAbs(body) => {
        removeTypeInEnv(env1, typ, env2, body)
        tabsInversionLemma(env1 ++ env2, TermTr.shift(body, -1, env1.size))
        check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
      }
      case TApp(body, typ2) => {
        removeTypeInEnv(env1, typ, env2, body)
        tappInversionLemma(env1 ++ env2, TermTr.shift(body, -1, env1.size), typ2)
        check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
      }
    }

    // assert(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    // OptionProperties.equalityImpliesDefined(
    //   typeOf(env1 ++ (typ :: env2), t), 
    //   typeOf(env1 ++ env2, TermTr.shift(t, -1, env1.size))
    // )
  }.ensuring(
    deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).isDefined 
    &&
    ( deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get )
  )

  @opaque @pure
  def preservationUnderSubst(env: Environment, t: Term, j: BigInt, s: Term): Unit = {
    require(deriveType(env, t).isDefined)
    require(deriveType(env, s).isDefined)
    require(0 <= j && j < env.size)
    require(env(j) == deriveType(env, s).get.t)

    t match {
      case Var(_) => assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      case Abs(typ, body) => {
        insertTypeInEnv(Nil(), typ, env, s)
        preservationUnderSubst(typ :: env, body, j+1, TermTr.shift(s, 1, 0))
        absInversionLemma(env, typ, body)
        absInversionLemma(env, typ, TermTr.substitute(body, j+1, TermTr.shift(s, 1, 0)))
        assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      }
      case App(t1, t2) => {
        preservationUnderSubst(env, t1, j, s)
        preservationUnderSubst(env, t2, j, s)
        appInversionLemma(env, t1, t2)
        appInversionLemma(env, TermTr.substitute(t1, j, s), TermTr.substitute(t2, j, s))
        assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      }
      case Fix(f) => {
        preservationUnderSubst(env, f, j, s)
        fixInversionLemma(env, f)
        fixInversionLemma(env, TermTr.substitute(f, j, s))
        assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      }
      case TAbs(body) => {
        preservationUnderSubst(env, body, j, s)
        tabsInversionLemma(env, body)
        tabsInversionLemma(env, TermTr.substitute(body, j, s))
        assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      }
      case TApp(body, typ) => {
        preservationUnderSubst(env, body, j, s)
        tappInversionLemma(env, body, typ)
        tappInversionLemma(env, TermTr.substitute(body, j, s), typ)
        assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
      }
    }
  }.ensuring(
    deriveType(env, TermTr.substitute(t, j, s)).isDefined &&
    (deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
  )

  @opaque @pure
  def preservationUnderAbsSubst(env: Environment, body: Term, arg: Term) = {
    require(deriveType(env, arg).isDefined)
    require(deriveType(deriveType(env, arg).get.t :: env, body).isDefined)

    
    // val Some(argType) = deriveType(env, arg)
    // val Some(typ) = deriveType(argType :: env, body)

    // insertTypeInEnv(Nil(), argType, env, arg)
    // assert(deriveType(argType :: env, TermTr.shift(arg, 1, 0)).get.t == argType)
    // preservationUnderSubst(argType :: env, body, 0, TermTr.shift(arg, 1, 0))

    // assert(!arg.hasFreeVariablesIn(0, 0))
    // TermTrProp.boundRangeShift(arg, 1, 0, 0)
    // TermTrProp.boundRangeSubstitutionLemma(body, 0, TermTr.shift(arg, 1, 0))
    // TermTrProp.boundRangeShiftBackLemma(TermTr.substitute(body, 0, TermTr.shift(arg, 1, 0)), 1, 0)
    // removeTypeInEnv(Nil(), argType, env, TermTr.substitute(body, 0, TermTr.shift(arg, 1, 0)))

  }.ensuring(deriveType(env, absSubsitution(body, arg)).get === deriveType(deriveType(env, arg).get.t :: env, body).get)

  @opaque @pure
  def preservationUnderTypeAbsSubst(env: Environment, body: Term, typ: Type) = {
    require(deriveType(env, body).isDefined)
    body match{
      case Var(k) => 
        assert(TypeTr.substitute(body, 0, TypeTr.shift(typ, 1, 0)) == body)
        assert(TypeTr.shift(body, 1, 0) == body)
      case Abs(targ, b) => ()
      case App(t1, t2) => ()
      case Fix(f) => ()
      case TAbs(b) => ()
      case TApp(b, t) => ()
    }
  }.ensuring(deriveType(env, tabsSubstitution(body, typ)).get.t == universalSubstitution(deriveType(env, body).get.t, typ))
  
  @opaque @pure
  def callByValuePreservationTheorem(env: Environment, t: Term): Unit = {
    require(deriveType(env, t).isDefined)
    require(reduceCallByValue(t).isDefined)
    val typeT = deriveType(env, t).get.t

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
        check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
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
        check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
      }
      case TAbs(_) => {
        check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
      }

      case TApp(term, typ) => 
        if(!term.isValue) {
          callByValuePreservationTheorem(env, term)
          check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
        }
        else {
          term match {
              case TAbs(body) => 
              //   assert(deriveType(env, reduceCallByValue(t).get).get === deriveType(env, tabsSubstitution(body, typ)).get)
              //   assert(deriveType(env, t).get === deriveType(env, TApp(TAbs(body), typ)).get)
              //   assert(deriveType(env, body).isDefined)
              //   assert(deriveType(env, term).get == UniversalType(typeOf(env, body).get.t))
              //   assert(deriveType(env, t).get == absSubstitution(typeOf(env, body).get.t, typ)) 
                preservationUnderTypeAbsSubst(env, body, typ)
                check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
              case _ => 
              check( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
              ()
          }
        }
        assert( deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get )
    }
  }.ensuring(
    deriveType(env, reduceCallByValue(t).get).isDefined &&
    (deriveType(env, reduceCallByValue(t).get).get === deriveType(env, t).get)
  )

}