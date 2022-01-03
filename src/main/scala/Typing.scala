import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Typing {
  import SystemF._
  import Reduction._
  import Transformations._

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
        case TAbsDerivation(env, UniversalType(b), TAbs(body), btd) => {
          btd.isValid && // Premise is valid
          btd.term == body && btd.env == Types.shift(env, 1, 0) && // and has matching attributes
          btd.t == b // The types are related as expected
        }
        case TAbsDerivation(_ ,_, _, _) => false
        case TAppDerivation(env, t, TApp(body, typ), btd) => {
          btd.isValid && // Premise is valid
          btd.term == body && btd.env == env &&  // and has matching attributes
          (btd.t match{
            case UniversalType(b) => t == universalSubstitution(b, typ)
            case _ => false
          })
        }
      }
    }
    
    def ===(that: TypeDerivation): Boolean = {
      this.t == that.t && this.env == that.env
    }
  }
  case class VarDerivation(e: Environment, typ: Type, ter: Var) extends TypeDerivation
  case class AbsDerivation(e: Environment, typ: Type, ter: Abs, btd: TypeDerivation) extends TypeDerivation
  case class AppDerivation(e: Environment, typ: Type, ter: App, btd1: TypeDerivation, btd2: TypeDerivation) extends TypeDerivation
  case class FixDerivation(e: Environment, typ: Type, ter: Fix, ftd: TypeDerivation) extends TypeDerivation
  case class TAbsDerivation(e: Environment, typ: Type, ter: TAbs, btd: TypeDerivation) extends TypeDerivation
  case class TAppDerivation(e: Environment, typ: Type, ter: TApp, btd: TypeDerivation) extends TypeDerivation


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
        deriveType(Types.shift(env, 1, 0), t) match{
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
  
  def deriveType(t: Term): Option[TypeDerivation] = {
    deriveType(Nil(), t)
  }

 }


object TypingProperties {
  import SystemF._
  import Typing._
  import Reduction._  
  import Transformations.{ Terms => TermTr, Types => TypeTr }

  import ListProperties._
  import SystemFProperties.{ Terms => TermProp, Types => TypeProp }
  import ReductionProperties._
  import TransformationsProperties.{ Terms => TermTrProp, Types => TypeTrProp }


  /// Type derivations
  @opaque @pure
  def deriveTypeCompleteness(@induct td: TypeDerivation): Unit = {
    require(td.isValid)
  }.ensuring(deriveType(td.env, td.term) == Some(td))

  @opaque @pure
  def deriveTypeValidity(env: Environment, t: Term): Unit = {
    require(deriveType(env, t).isDefined)
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
        deriveTypeValidity(TypeTr.shift(env, 1, 0), t)
      }
      case TApp(t, typ) => {
        deriveTypeValidity(env, t)
      }
    }
  }.ensuring(
    deriveType(env, t).get.isValid && 
    deriveType(env, t).get.term == t && 
    deriveType(env, t).get.env == env
  )

  @opaque @pure
  def typeDerivationsUniqueness(td1: TypeDerivation, td2: TypeDerivation): Unit = {
    require(td1.isValid)
    require(td2.isValid)
    require(td1.term == td2.term)
    require(td1.env == td2.env)

    deriveTypeCompleteness(td1)
    deriveTypeCompleteness(td2)
  }.ensuring(td1 == td2)

  /// Progress
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


  /// Preservation
  @extern
  def aSsUmE(b: Boolean): Unit = {}.ensuring(b)

  @extern
  def mAgIcDeRiVaTiOn(p: TypeDerivation => Boolean): TypeDerivation = {
    VarDerivation(Nil(), BasicType(""), Var(0)) : TypeDerivation
  }.ensuring(p(_))

  

  @opaque @pure
  def environmentWeakening(td: TypeDerivation, envExt: Environment): TypeDerivation = {
    require(td.isValid)
    td match {
      case VarDerivation(env, typ, Var(k)) => {
        concatFirstIndexing(env, envExt, k)
        VarDerivation(env ++ envExt, typ, Var(k))
      }
      case AbsDerivation(env, typ, Abs(argType, body), btd) => {
        val resBtd = environmentWeakening(btd, envExt)
        AbsDerivation(env ++ envExt, typ, Abs(argType, body), resBtd)
      }
      case AppDerivation(env, typ, App(t1, t2), bt1, bt2) => {
        val resBt1 = environmentWeakening(bt1, envExt)
        val resBt2 = environmentWeakening(bt2, envExt)
        AppDerivation(env ++ envExt, typ, App(t1, t2), resBt1, resBt2)
      }
      case FixDerivation(env, typ, Fix(f), ftd) => {
        val resFtd = environmentWeakening(ftd, envExt)
        FixDerivation(env ++ envExt, typ, Fix(f), resFtd)
      }
      case TAbsDerivation(env, typ, TAbs(body), btd) => {
        ListProperties.mapConcat(env, envExt, Transformations.Types.shift(_: Type, 1, 0))
        val resBtd = environmentWeakening(btd,  TypeTr.shift(envExt, 1, 0))
        TAbsDerivation(env ++ envExt, typ, TAbs(body), resBtd)
      }
      case TAppDerivation(env, typ, TApp(body, argType), btd) => {
        val resBtd = environmentWeakening(btd, envExt)
        TAppDerivation(env ++ envExt, typ, TApp(body, argType), resBtd)
      }
    }
  }.ensuring(res => res.isValid && res.env == td.env ++ envExt && res.term == td.term && res.t == td.t)

  @opaque @pure
  def variableEnvironmentStrengthening(v: VarDerivation, env: Environment, envExt: Environment): VarDerivation = {
    require(v.env == env ++ envExt)
    require(v.isValid)
    require(v.ter.k < env.length)
    concatFirstIndexing(env, envExt, v.ter.k)
    VarDerivation(env, v.typ, v.ter)
  }.ensuring(res => res.isValid && res.env == env && res.typ == v.typ && res.ter == v.ter)

  @opaque @pure
  def variableEnvironmentUpdate(v: VarDerivation, env: Environment, oldEnv: Environment, newEnv: Environment): VarDerivation = {
    require(v.env == env ++ oldEnv)
    require(v.isValid)
    require(v.ter.k < env.length)  
    val v2 = variableEnvironmentStrengthening(v, env, oldEnv) 
    environmentWeakening(v2, newEnv)
    VarDerivation(env ++ newEnv, v.typ, v.ter)
  }.ensuring(res => res.isValid && res.env == env ++ newEnv && res.typ == v.typ && res.ter == v.ter)

  // WIP
  @opaque @pure
  def insertTypeInEnv(env1: Environment, typ: Type, env2: Environment, td: TypeDerivation): TypeDerivation = {
    require(td.isValid)
    require(env1 ++ env2 == td.env)

    td match {
      case v@VarDerivation(env, typ, Var(k)) => {
        if (k < env1.size){
          variableEnvironmentUpdate(v, env1, env2, (typ :: env2))
          val res = VarDerivation(env1 ++ (typ :: env2), typ, Var(k))
          assert(res.isValid)
          assert( res.term == TermTr.shift(td.term, 1, env1.size) )
          assert( res.env == env1 ++ (typ :: env2) )
          assert( td.t == res.t )
          res
        }
        else{
          insertionIndexing(env1, env2, typ, k)
          val res = VarDerivation(env1 ++ (typ :: env2), typ, Var(k + 1))
          assert(res.isValid)
          assert( res.term == TermTr.shift(td.term, 1, env1.size) )
          assert( res.env == env1 ++ (typ :: env2) )
          assert( td.t == res.t )
          res
         }
      }
      case AbsDerivation(env, typ, Abs(argType, body), btd) => {
        val resBtd = insertTypeInEnv(argType :: env1, typ, env2, btd)
        val res = AbsDerivation(env1 ++ (typ :: env2), typ, Abs(argType, TermTr.shift(body, 1, env1.size + 1)), resBtd)
        assert(res.isValid)
        assert( res.term == TermTr.shift(td.term, 1, env1.size) )
        assert( res.env == env1 ++ (typ :: env2) )
        assert( td.t == res.t )
        res
      }
      case AppDerivation(env, typ, App(t1, t2), td1, td2) => {
        val resTd1 = insertTypeInEnv(env1, typ, env2, td1)
        val resTd2 = insertTypeInEnv(env1, typ, env2, td2)
        val res = AppDerivation(env1 ++ (typ :: env2), typ, App(TermTr.shift(t1, 1, env1.size), TermTr.shift(t2, 1, env1.size)), resTd1, resTd2)
        assert(res.isValid)
        assert( res.term == TermTr.shift(td.term, 1, env1.size) )
        assert( res.env == env1 ++ (typ :: env2) )
        assert( td.t == res.t )
        res
      }
      case FixDerivation(env, typ, Fix(f), ftd) => {
        val resFtd = insertTypeInEnv(env1, typ, env2, ftd)
        val res = FixDerivation(env1 ++ (typ :: env2), typ, Fix(TermTr.shift(f, 1, env1.size)), resFtd)
        assert(res.isValid)
        assert( res.term == TermTr.shift(td.term, 1, env1.size) )
        assert( res.env == env1 ++ (typ :: env2) )
        assert( td.t == res.t )
        res
      }
      case TAbsDerivation(env, typ, TAbs(body), btd) => {
        ListProperties.mapPrepend(typ, env2, Transformations.Types.shift(_: Type, 1, 0))
        ListProperties.mapConcat(env1, typ :: env2, Transformations.Types.shift(_: Type, 1, 0))
        ListProperties.mapConcat(env1, env2, Transformations.Types.shift(_: Type, 1, 0))
        val resBtd = insertTypeInEnv(TypeTr.shift(env1, 1, 0), TypeTr.shift(typ, 1, 0), TypeTr.shift(env2, 1, 0), btd)
        val res = TAbsDerivation(env1 ++ (typ :: env2), typ, TAbs(TermTr.shift(body, 1, env1.size)), resBtd)
        assert(res.isValid)
        assert( res.term == TermTr.shift(td.term, 1, env1.size) )
        assert( res.env == env1 ++ (typ :: env2) )
        assert( td.t == res.t )
        res
      }
      case TAppDerivation(env, typ, TApp(body, typeArg), btd) => {
        val resBtd = insertTypeInEnv(env1, typ, env2, btd)
        val res = TAppDerivation(env1 ++ (typ :: env2), typ, TApp(TermTr.shift(body, 1, env1.size), typeArg), resBtd)
        assert(res.isValid)
        assert( res.term == TermTr.shift(td.term, 1, env1.size) )
        assert( res.env == env1 ++ (typ :: env2) )
        assert( td.t == res.t )
        res
      }
    }
    
  }.ensuring(res =>
    res.isValid &&
    ( res.term == TermTr.shift(td.term, 1, env1.size) ) &&
    ( res.env == env1 ++ (typ :: env2) ) &&
    ( td.t == res.t )
  )

  // WIP
  @extern
  def removeTypeInEnv(env1: Environment, typ: Type, env2: Environment, td: TypeDerivation): TypeDerivation = {
    require(td.isValid)
    require(td.env == env1 ++ (typ :: env2))
    require(!td.term.hasFreeVariablesIn(env1.size, 1))

    // TermTrProp.boundRangeShiftBackLemma(t, 1, env1.size)
    // t match {
    //   case Var(k) => {
    //     if (k < env1.size) {
    //       variableEnvironmentUpdate(Var(k), env1, typ :: env2, env2)
    //       check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //     }
    //     else {
    //       insertionIndexing(env1, env2, typ, k - 1)
    //       check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //     }
    //   }
    //   case Abs(targ, body) => {
    //     absInversionLemma(env1 ++ (typ :: env2), targ, body)
    //     removeTypeInEnv(targ :: env1, typ, env2, body)
    //     absInversionLemma(env1 ++ env2, targ, TermTr.shift(body, -1, env1.size + 1))
    //     check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //   }
    //   case App(t1, t2) => {
    //     appInversionLemma(env1 ++ (typ :: env2), t1, t2)
    //     removeTypeInEnv(env1, typ, env2, t2)
    //     removeTypeInEnv(env1, typ, env2, t1)
    //     appInversionLemma(env1 ++ env2, TermTr.shift(t1, -1, env1.size), TermTr.shift(t2, -1, env1.size))
    //     assert(App(TermTr.shift(t1, -1, env1.size), TermTr.shift(t2, -1, env1.size)) == TermTr.shift(t, -1, env1.size))
    //     check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //   }
    //   case Fix(f) => {
    //     removeTypeInEnv(env1, typ, env2, f)
    //     fixInversionLemma(env1 ++ env2, TermTr.shift(f, -1, env1.size))
    //     check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //   }
    //   case TAbs(body) => {
    //     tabsInversionLemma(env1 ++ (typ :: env2), body)
    //     ListProperties.mapPrepend(typ, env2, Transformations.Types.shift(_: Type, 1, 0))
    //     ListProperties.mapConcat(env1, typ :: env2, Transformations.Types.shift(_: Type, 1, 0))
    //     ListProperties.mapConcat(env1, env2, Transformations.Types.shift(_: Type, 1, 0))
    //     removeTypeInEnv(shift(env1, 1, 0), TypeTr.shift(typ, 1, 0), shift(env2, 1, 0), body)
    //     tabsInversionLemma(env1 ++ env2, TermTr.shift(body, -1, env1.size))
    //     check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //   }
    //   case TApp(body, typ2) => {
    //     removeTypeInEnv(env1, typ, env2, body)
    //     tappInversionLemma(env1 ++ env2, TermTr.shift(body, -1, env1.size), typ2)
    //     check(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    //   }
    // }

    // assert(deriveType(env1 ++ (typ :: env2), t).get === deriveType(env1 ++ env2, TermTr.shift(t, -1, env1.size)).get)
    // OptionProperties.equalityImpliesDefined(
    //   typeOf(env1 ++ (typ :: env2), t), 
    //   typeOf(env1 ++ env2, TermTr.shift(t, -1, env1.size))
    // )

    mAgIcDeRiVaTiOn(_ => true)
  }.ensuring(res =>
    res.isValid &&
    ( res.term == TermTr.shift(td.term, -1, env1.size) ) &&
    ( res.env == env1 ++ env2 ) &&
    ( td.t == res.t)
  )

  // WIP
  @opaque @pure
  def shiftTypesInEnv(td: TypeDerivation, s: BigInt): TypeDerivation = {
    require(td.isValid)
    require(s >= 0 || TypeTr.negativeShiftValidity(td.env, s, 0))
    require(s >= 0 || TypeTr.negativeShiftValidity(td.term, s, 0))
    require(s >= 0 || TypeTr.negativeShiftValidity(td.t, s, 0))

    val p = (res: TypeDerivation) => {
      res.isValid &&
      ( res.env == TypeTr.shift(td.env, s, 0) ) &&
      ( res.term == TypeTr.shift(td.term, s, 0) ) &&
      ( res.t == TypeTr.shift(td.t, s, 0) )
    }

    val newEnv = TypeTr.shift(td.env, s, 0)
    val newTyp = TypeTr.shift(td.t, s, 0)
    val newTerm = TypeTr.shift(td.term, s, 0)

    td match {
      case VarDerivation(env, typ, Var(k)) => {
        assert(env(k) == typ)
        assert(newTerm.isInstanceOf[Var])
        ListProperties.mapIndexing(k, env, TypeTr.shift(_: Type, s, 0))
        VarDerivation(newEnv, newTyp, newTerm.asInstanceOf[Var])
      }
      case AbsDerivation(env, typ, Abs(argType, body), btd) => {
        mAgIcDeRiVaTiOn(p)
      }
      case AppDerivation(_, _, _, td1, td2) => {
        assert(s >= 0 || TypeTr.negativeShiftValidity(td1.t, s, 0))
        assert(s >= 0 || TypeTr.negativeShiftValidity(td2.t, s, 0))
        val td1p = shiftTypesInEnv(td1, s)
        val td2p = shiftTypesInEnv(td2, s)
        AppDerivation(newEnv, newTyp, App(td1p.term, td2p.term), td1p, td2p)
      }
      case FixDerivation(_, _, _, ftd) => {
        val ftdp = shiftTypesInEnv(ftd, s)
        FixDerivation(newEnv, newTyp, Fix(ftdp.term), ftdp)
      }
      case TAbsDerivation(_, _, _, btd) => {
        val btdp = shiftTypesInEnv(btd, s)
        TAbsDerivation(newEnv, newTyp, TAbs(btdp.term), btdp)
      }
      case TAppDerivation(_, _, TApp(_, typeArg), btd) => {
        val btdp = shiftTypesInEnv(btd, s)
        TAppDerivation(newEnv, newTyp, TApp(btdp.term, TypeTr.shift(typeArg, s, 0)), btdp)
      }
    }
  }.ensuring(res =>
    res.isValid &&
    ( res.env == TypeTr.shift(td.env, s, 0) ) &&
    ( res.term == TypeTr.shift(td.term, s, 0) ) &&
    ( res.t == TypeTr.shift(td.t, s, 0) )
  )

  // WIP
  @opaque @pure
  def preservationUnderSubst(td: TypeDerivation, j: BigInt, sd: TypeDerivation): TypeDerivation = {
    require(td.isValid)
    require(sd.isValid)
    require(td.env == sd.env)
    require(0 <= j && j < td.env.size)
    require(td.env(j) == sd.t)

    val result = TermTr.substitute(td.term, j, sd.term)

    val p = (deriv: TypeDerivation) => {
      deriv.isValid && deriv === td && deriv.term == result
    }

    td match {
      case VarDerivation(env, typ, Var(k)) => {
        if(j == k) {
          assert(result == sd.term)
          assert(p(sd))
          sd
        }
        else {
          assert(result == td.term)
          assert(p(td))
          td
        }
      }
      case AbsDerivation(env, typ, Abs(argType, body), btd) => {
        val d0 = insertTypeInEnv(Nil(), argType, td.env, sd)
        assert(btd.env == argType :: td.env)
        val d1 = preservationUnderSubst(btd, j+1, d0)
        val d = AbsDerivation(env, typ, Abs(argType, d1.term), d1)
        assert(p(d))
        d
      }
      case AppDerivation(env, typ, App(t1, t2), td1, td2) => {
        val td1p = preservationUnderSubst(td1, j, sd)
        val td2p = preservationUnderSubst(td2, j, sd)
        val d = AppDerivation(env, typ, App(td1p.term, td2p.term), td1p, td2p)
        assert(p(d))
        d
      }
      case FixDerivation(env, typ, Fix(f), ftd) => {
        val ftdp = preservationUnderSubst(ftd, j, sd)
        val d = FixDerivation(env, typ, Fix(ftdp.term), ftdp)
        assert(p(d))
        d
      }
      case TAbsDerivation(env, typ, TAbs(body), btd) => {
        /// Lacks a shift in environment
        // val btdp = preservationUnderSubst(btd, j, sd)
        // val d = TAbsDerivation(env, typ, TAbs(btdp.term), btdp)
        // assert(p(d))
        // d
        mAgIcDeRiVaTiOn(p)
      }
      case TAppDerivation(env, typ, TApp(body, typeArg), btd) => {
        val btdp = preservationUnderSubst(btd, j, sd)
        val d = TAppDerivation(env, typ, TApp(btdp.term, typeArg), btdp)
        assert(p(d))
        d
      }
    }

  }.ensuring(res =>
    res.isValid &&
    ( res.term == TermTr.substitute(td.term, j, sd.term) ) &&
    ( td === res )
  )

  // WIP
  @opaque @pure
  def shiftSubstitutionCommutativityType(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    require(s >= 0)
    require(k >= 0)
    require(c >= 0 && c <= k)

    typ match {
      case BasicType(_) => {
        assert(TypeTr.shift(TypeTr.substitute(typ, k, subs), s, c) == typ)
        assert(TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c)) == typ)
      }
      case ArrowType(t1, t2) => {
        shiftSubstitutionCommutativityType(t1, s, c, k, subs)
        shiftSubstitutionCommutativityType(t2, s, c, k, subs)
      }
      case VariableType(v) => {
        if(v == k) {
          assert(TypeTr.shift(TypeTr.substitute(typ, k, subs), s, c) == TypeTr.shift(subs, s, c))
          assert(TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c)) == TypeTr.shift(subs, s, c))
        }
        else {
          assert(TypeTr.shift(TypeTr.substitute(typ, k, subs), s, c) == TypeTr.shift(typ, s, c))
          assert(TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c)) == TypeTr.shift(typ, s, c))
        }
      }
      case UniversalType(t) => {
        assert(
          TypeTr.shift(TypeTr.substitute(typ, k, subs), s, c) 
          == 
          UniversalType( TypeTr.shift(TypeTr.substitute(t, k+1, TypeTr.shift(subs, 1, 0)), s, c+1)  )
        )
        assert(
          TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c))
          ==
          UniversalType( TypeTr.substitute(TypeTr.shift(t, s, c+1), k+1+s, TypeTr.shift(TypeTr.shift(subs, s, c), 1, 0)) )
        )
        // Might be useful: TypeTrProp.boundRangeShiftComposition
        assert(
          TypeTr.shift(TypeTr.shift(subs, s, c), 1, 0)
          ==
          TypeTr.shift(TypeTr.shift(subs, 1, 0), s, c+1)
        )
        assert(
          TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c))
          ==
          UniversalType( TypeTr.substitute(TypeTr.shift(t, s, c+1), k+1+s, TypeTr.shift(TypeTr.shift(subs, 1, 0), s, c+1)) )
        )
        shiftSubstitutionCommutativityType(t, s, c+1, k+1, TypeTr.shift(subs, 1, 0))
        assert(
          TypeTr.shift(TypeTr.substitute(t, k+1, TypeTr.shift(subs, 1, 0)), s, c+1)
          ==
          TypeTr.substitute(TypeTr.shift(t, s, c+1), k+1+s, TypeTr.shift(TypeTr.shift(subs, 1, 0), s, c+1))
        )
        assert(
          UniversalType( TypeTr.shift(TypeTr.substitute(t, k+1, TypeTr.shift(subs, 1, 0)), s, c+1)  )
          ==
          UniversalType( TypeTr.substitute(TypeTr.shift(t, s, c+1), k+1+s, TypeTr.shift(TypeTr.shift(subs, 1, 0), s, c+1)) )
        )
        // Might need some additional calls to fit exactly our needs
      }
    }
  }.ensuring(
    TypeTr.shift(TypeTr.substitute(typ, k, subs), s, c) 
    == 
    TypeTr.substitute(TypeTr.shift(typ, s, c), k+s, TypeTr.shift(subs, s, c))
  )

  @opaque @pure
  def shiftSubstitutionCommutativity(env: Environment, s: BigInt, k: BigInt, subs: Type): Unit = {
    require(s >= 0)
    require(k >= 0)
    env match {
      case Nil() => {
        assert(TypeTr.shift(TypeTr.substitute(env, k, subs), s, 0) == Nil())
        assert(TypeTr.substitute(TypeTr.shift(env, s, 0), k+s, TypeTr.shift(subs, s, 0)) == Nil())
      }
      case Cons(h, t) => {
        shiftSubstitutionCommutativityType(h, s, 0, k, subs)
        shiftSubstitutionCommutativity(t, s, k, subs)
      }
    }
  }.ensuring(
    TypeTr.shift(TypeTr.substitute(env, k, subs), s, 0) 
    == 
    TypeTr.substitute(TypeTr.shift(env, s, 0), k+s, TypeTr.shift(subs, s, 0))
  )

  // WIP
  @opaque @pure
  def preservationUnderTypeSubst(td: TypeDerivation, j: BigInt, styp: Type): TypeDerivation = {
    require(td.isValid)

    val newEnv = TypeTr.substitute(td.env, j, styp)
    val newTyp = TypeTr.substitute(td.t, j, styp)

    td match {
      case VarDerivation(env, typ, Var(k)) => {
        assert(env(k) == typ)
        ListProperties.mapIndexing(k, env, TypeTr.substitute(_: Type, j, styp))
        VarDerivation(newEnv, newTyp, Var(k))
      }
      case AbsDerivation(_, typ, Abs(argType, _), btd) => {
        val btdp = preservationUnderTypeSubst(btd, j, styp)
        val argTypep = TypeTr.substitute(argType, j, styp)
        ListProperties.mapPrepend(argType, btd.env, TypeTr.substitute(_: Type, j, styp))
        AbsDerivation(newEnv, newTyp, Abs(argTypep, btdp.term), btdp)
      }
      case AppDerivation(_, typ, App(_, _), td1, td2) => {
        val td1p = preservationUnderTypeSubst(td1, j, styp)
        val td2p = preservationUnderTypeSubst(td2, j, styp)
        AppDerivation(newEnv, newTyp, App(td1p.term, td2p.term), td1p, td2p)
      }
      case FixDerivation(_, typ, Fix(_), ftd) => {
        val ftdp = preservationUnderTypeSubst(ftd, j, styp)
        FixDerivation(newEnv, newTyp, Fix(ftdp.term), ftdp)
      }
      case TAbsDerivation(_, typ, TAbs(_), btd) => {
        val btdp = preservationUnderTypeSubst(btd, j+1, TypeTr.shift(styp, 1, 0))
        shiftSubstitutionCommutativity(td.env, 1, j, styp)
        TAbsDerivation(newEnv, newTyp, TAbs(btdp.term), btdp)
      }
      case TAppDerivation(_, typ, TApp(_, argType), btd) => {
        // val btdp = preservationUnderTypeSubst(btd, j, styp)
        // val newArg = TypeTr.substitute(argType, j, styp)
        // assert(btdp.t.isInstanceOf[UniversalType])
        // val UniversalType(bodyType) = btd.t
        // val UniversalType(newBodyType) = btdp.t
        // assert(typ == universalSubstitution(bodyType, argType))
        // assert(newTyp == universalSubstitution(newBodyType, newArg))
        // val res = TAppDerivation(newEnv, newTyp, TApp(btdp.term, newArg), btdp)
        
        // assert(  res.isValid )
        // assert( res.term == TypeTr.substitute(td.term, j, styp) ) 
        // assert( res.env == substitute(td.env, j, styp) ) 
        // assert( res.t == TypeTr.substitute(td.t, j, styp) )
        // res
        mAgIcDeRiVaTiOn(res =>
          res.isValid &&
          ( res.term == TypeTr.substitute(td.term, j, styp) ) &&
          ( res.env == TypeTr.substitute(td.env, j, styp) ) &&
          ( res.t == TypeTr.substitute(td.t, j, styp) )
        )
      }
    }

  }.ensuring(res =>
    res.isValid &&
    ( res.term == TypeTr.substitute(td.term, j, styp) ) &&
    ( res.env == TypeTr.substitute(td.env, j, styp) ) &&
    ( res.t == TypeTr.substitute(td.t, j, styp) )
  )

  @opaque @pure
  def preservationUnderAbsSubst(env: Environment, absTd: AbsDerivation, argTd: TypeDerivation, typ: Type): TypeDerivation = {
    require(absTd.isValid && argTd.isValid)
    require(absTd.env == env && argTd.env == env)
    require(absTd.ter.argType == argTd.t)
    require(absTd.t == ArrowType(argTd.t, typ))

    val Abs(argType, _) = absTd.term

    val sd0 = argTd
    val sd1 = insertTypeInEnv(Nil(), argType, sd0.env, sd0)
    val sd2 = preservationUnderSubst(absTd.btd, 0, sd1)

    assert(!sd0.term.hasFreeVariablesIn(0, 0))
    TermTrProp.boundRangeShift(sd0.term, 1, 0, 0)
    TermTrProp.boundRangeSubstitutionLemma(absTd.btd.term, 0, sd1.term)
    TermTrProp.boundRangeShiftBackLemma(sd2.term, 1, 0)
    removeTypeInEnv(Nil(), argType, env, sd2)
  }.ensuring(res => 
    res.isValid &&
    ( res.term == absSubstitution(absTd.ter.body, argTd.term) ) &&
    ( res.env == env ) &&
    ( res.t == typ )
  )

  @opaque @pure
  def preservationUnderTAbsSubst(tabsTd: TAbsDerivation, arg: Type, typ: Type): TypeDerivation = {
    require(tabsTd.isValid)
    require(typ == universalSubstitution(tabsTd.btd.t, arg))

    val td0 = tabsTd.btd
    val td1 = preservationUnderTypeSubst(td0, 0, TypeTr.shift(arg, 1, 0))

    assert(!arg.hasFreeVariablesIn(0, 0))
    TypeTrProp.boundRangeShift(arg, 1, 0, 0)

    // Environment
    TypeTrProp.boundRangeShift(tabsTd.env, 1, 0, 0)
    TypeTrProp.boundRangeSubstitutionIdentity(td0.env, 0, TypeTr.shift(arg, 1, 0))
    TypeTrProp.boundRangeShiftComposition(tabsTd.env, 1, -1, 0, 0)
    TypeTrProp.shift0Identity(tabsTd.env, 0)

    // Term
    TypeTrProp.boundRangeSubstitutionLemma(td0.term, 0, TypeTr.shift(arg, 1, 0))
    TypeTrProp.boundRangeShiftBackLemma(td1.term, 1, 0)

    // Type
    TypeTrProp.boundRangeSubstitutionLemma(typ, 0, TypeTr.shift(arg, 1, 0))
    TypeTrProp.boundRangeShiftBackLemma(TypeTr.substitute(typ, 0, TypeTr.shift(arg, 1, 0)), 1, 0)

    TypeTrProp.boundRangeShiftBackLemma(td1.env, 1, 0)
    shiftTypesInEnv(td1, -1)
  }.ensuring(res =>
    res.isValid &&
    ( res.term == tabsSubstitution(tabsTd.btd.term, arg) ) &&
    ( res.env == tabsTd.env ) &&
    ( res.t == typ )
  )

  @opaque @pure
  def absDerivationInversion(td: TypeDerivation): Unit = {
    require(td.term.isInstanceOf[Abs])
  }.ensuring(td.isInstanceOf[AbsDerivation])

  @opaque @pure
  def reductionPreservationTheorem(td: TypeDerivation, reduced: Term): TypeDerivation = {
    require(td.isValid)
    require(reducesTo(td.term, reduced).isDefined)
    decreases(td)

    val Some(rule) = reducesTo(td.term, reduced)

    td match {
      case AppDerivation(env, typ, t@App(t1, t2), td1, td2) => {

        assert(td.term == t)
        appReducesToSoundness(t, reduced)
        rule match {
          case App1Congruence => {
            app1CongruenceInversion(t, reduced)
            val tp = reduced.asInstanceOf[App]
            val t1p = tp.t1

            val td1p = reductionPreservationTheorem(td1, t1p)
            val tdp = AppDerivation(env, typ, tp, td1p, td2)
            assert(td1p.isValid && td2.isValid)
            assert(tp == App(td1p.term, td2.term))
            assert(tdp.isValid)
            tdp
          }
          case App2Congruence => {
            app2CongruenceInversion(t, reduced)
            val tp = reduced.asInstanceOf[App]
            val t2p = tp.t2
            
            val td2p = reductionPreservationTheorem(td2, t2p)
            val tdp = AppDerivation(env, typ, tp, td1, td2p)
            assert(tdp.isValid)
            tdp
          }
          case AbsAppReduction => {
            absAppReductionInversion(t, reduced)
            absDerivationInversion(td1)
            preservationUnderAbsSubst(env, td1.asInstanceOf[AbsDerivation], td2, typ)
          }
        }
      }
      case FixDerivation(env, typ, t@Fix(f), ftd) => {

        assert(td.term == t)
        fixReducesToSoundness(t, reduced)
        rule match {
          case FixCongruence => {
            fixCongruenceInversion(t, reduced)
            val tp = reduced.asInstanceOf[Fix]
            val fp = tp.t

            val ftdp = reductionPreservationTheorem(ftd, fp)
            val tdp = FixDerivation(env, typ, tp, ftdp)
            assert(tdp.isValid)
            tdp
          }
          case AbsFixReduction => {
            absFixReductionInversion(t, reduced)
            absDerivationInversion(ftd)
            preservationUnderAbsSubst(env, ftd.asInstanceOf[AbsDerivation], td, typ)
          }
        }
      }
      case TAppDerivation(env, typ, t@TApp(body, typeArg), btd) => {

        tappReducesToSoundness(t, reduced)
        rule match {
          case TAppCongruence => {
            tappCongruenceInversion(t, reduced)
            val tp = reduced.asInstanceOf[TApp]

            val btdp = reductionPreservationTheorem(btd, tp.t)
            val tdp = TAppDerivation(env, typ, tp, btdp)
            assert(tdp.isValid)
            tdp
          }
          case TAbsTappReduction => {
            tabsTappReductionInversion(t, reduced)
            preservationUnderTAbsSubst(btd.asInstanceOf[TAbsDerivation], typeArg, typ)
          }
        }
      }
    }

  }.ensuring(res => 
    res.isValid &&
    ( res.term == reduced ) &&
    ( res === td )
  )

}