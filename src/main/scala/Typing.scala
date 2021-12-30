import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Typing {
  import SystemF._
  import Reduction._

  type Environment = List[Type]

  def shift(env: Environment, d: BigInt, c: BigInt): Environment = {
    require(d >= 0)
    require(c >= 0)
    env.map(Transformations.Types.shift(_, d, c))
  }

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
          btd.term == body && btd.env == shift(env, 1, 0) && // and has matching attributes
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
        deriveType(shift(env, 1, 0), t) match{
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
        deriveTypeValidity(shift(env, 1, 0), t)
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
  def insertTypeInEnv(env1: Environment, typ: Type, env2: Environment, td: TypeDerivation): Unit = {
    require(td.isValid)
    require(env1 ++ env2 == td.env)

    // t match{
    //   case Var(k) => {
    //     if (k < env1.size){
    //       variableEnvironmentUpdate(Var(k), env1, env2, (typ :: env2))
    //       check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //     }
    //     else{
    //       insertionIndexing(env1, env2, typ, k)
    //       check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //     }
    //   }
    //   case Abs(targ, body) => {
    //     absInversionLemma(env1 ++ env2, targ, body)
    //     insertTypeInEnv(targ :: env1, typ, env2, body)
    //     absInversionLemma(env1 ++ (typ :: env2), targ, TermTr.shift(body, 1, env1.size + 1))
    //     check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //   }
    //   case App(t1, t2) => {
    //     appInversionLemma(env1 ++ env2, t1, t2)
    //     insertTypeInEnv(env1, typ, env2, t2)
    //     insertTypeInEnv(env1, typ, env2, t1)
    //     appInversionLemma(env1 ++ (typ :: env2), TermTr.shift(t1, 1, env1.size), TermTr.shift(t2, 1, env1.size))
    //     check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //   }
    //   case Fix(f) => {
    //     fixInversionLemma(env1 ++ env2, f)
    //     insertTypeInEnv(env1, typ, env2, f)
    //     fixInversionLemma(env1 ++ (typ :: env2), TermTr.shift(f, 1, env1.size))
    //     check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //   }
    //   case TAbs(body) => {
    //     tabsInversionLemma(env1 ++ env2, body)
    //     ListProperties.mapPrepend(typ, env2, Transformations.Types.shift(_: Type, 1, 0))
    //     ListProperties.mapConcat(env1, typ :: env2, Transformations.Types.shift(_: Type, 1, 0))
    //     ListProperties.mapConcat(env1, env2, Transformations.Types.shift(_: Type, 1, 0))
    //     insertTypeInEnv(shift(env1, 1, 0), TypeTr.shift(typ, 1, 0), shift(env2, 1, 0), body)
    //     tabsInversionLemma(env1 ++ (typ :: env2), TermTr.shift(body, 1, env1.size))
    //     check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //   }
    //   case TApp(body, typ2) => {
    //     tappInversionLemma(env1 ++ env2, body, typ2)
    //     insertTypeInEnv(env1, typ, env2, body)
    //     tappInversionLemma(env1 ++ (typ :: env2), TermTr.shift(body, 1, env1.size), typ2)
    //     check(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    //   }
    // }

    // assert(deriveType(env1 ++ env2, t).get === deriveType(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)).get)
    // OptionProperties.equalityImpliesDefined(
    //   typeOf(env1 ++ env2, t),
    //   typeOf(env1 ++ (typ :: env2), TermTr.shift(t, 1, env1.size)), 
    // )
  }.ensuring(
    deriveType(env1 ++ (typ :: env2),  TermTr.shift(td.term, 1, env1.size)).isDefined && 
    (td === deriveType(env1 ++ (typ :: env2),  TermTr.shift(td.term, 1, env1.size)).get)
  )

  @extern
  def removeTypeInEnv(env1: Environment, typ: Type, env2: Environment, td: TypeDerivation): Unit = {
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
  }.ensuring(
    deriveType(env1 ++ env2, TermTr.shift(td.term, -1, env1.size)).isDefined &&
    (td === deriveType(env1 ++ env2, TermTr.shift(td.term, -1, env1.size)).get)
  )

  @extern
  def preservationUnderSubst(td: TypeDerivation, j: BigInt, sd: TypeDerivation): Unit = {
    require(td.isValid)
    require(sd.isValid)
    require(td.env == sd.env)
    require(0 <= j && j < td.env.size)
    require(td.env(j) == sd.t)

    // td match {
    //   case Var(_) => assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   case Abs(typ, body) => {
    //     insertTypeInEnv(Nil(), typ, env, s)
    //     preservationUnderSubst(typ :: env, body, j+1, TermTr.shift(s, 1, 0))
    //     absInversionLemma(env, typ, body)
    //     absInversionLemma(env, typ, TermTr.substitute(body, j+1, TermTr.shift(s, 1, 0)))
    //     assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   }
    //   case App(t1, t2) => {
    //     preservationUnderSubst(env, t1, j, s)
    //     preservationUnderSubst(env, t2, j, s)
    //     appInversionLemma(env, t1, t2)
    //     appInversionLemma(env, TermTr.substitute(t1, j, s), TermTr.substitute(t2, j, s))
    //     assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   }
    //   case Fix(f) => {
    //     preservationUnderSubst(env, f, j, s)
    //     fixInversionLemma(env, f)
    //     fixInversionLemma(env, TermTr.substitute(f, j, s))
    //     assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   }
    //   case TAbs(body) => {
    //     preservationUnderSubst(shift(env, 1, 0), body, j, s)
    //     tabsInversionLemma(env, body)
    //     tabsInversionLemma(env, TermTr.substitute(body, j, s))
    //     assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   }
    //   case TApp(body, typ) => {
    //     preservationUnderSubst(env, body, j, s)
    //     tappInversionLemma(env, body, typ)
    //     tappInversionLemma(env, TermTr.substitute(body, j, s), typ)
    //     assert(deriveType(env, t).get === deriveType(env, TermTr.substitute(t, j, s)).get)
    //   }
    // }
  }.ensuring(
    deriveType(td.env, TermTr.substitute(td.term, j, sd.term)).isDefined &&
    (td === deriveType(td.env, TermTr.substitute(td.term, j, sd.term)).get)
  )

  @opaque @pure
  def preservationUnderAbsSubst(env: Environment, absTd: AbsDerivation, argTd: TypeDerivation, typ: Type) = {
    require(absTd.isValid && argTd.isValid)
    require(absTd.env == env && argTd.env == env)
    require(absTd.ter.argType == argTd.t)
    require(absTd.t == ArrowType(argTd.t, typ))

    val Abs(argType, _) = absTd.term
    val s0 = absTd.btd.term
    val arg = argTd.term

    insertTypeInEnv(Nil(), argType, argTd.env, argTd)
    //assert(hasType(argType :: env, TermTr.shift(arg, 1, 0), argType))

    deriveTypeValidity(argType :: env, TermTr.shift(arg, 1, 0))
    preservationUnderSubst(absTd.btd, 0, deriveType(argType :: env, TermTr.shift(arg, 1, 0)).get)
    val s1 = TermTr.substitute(s0, 0, TermTr.shift(arg, 1, 0))
    //assert(hasType(argType :: env, s1, absTd.btd.t))

    assert(!arg.hasFreeVariablesIn(0, 0))
    TermTrProp.boundRangeShift(arg, 1, 0, 0)
    TermTrProp.boundRangeSubstitutionLemma(s0, 0, TermTr.shift(arg, 1, 0))
    TermTrProp.boundRangeShiftBackLemma(s1, 1, 0)
    deriveTypeValidity(argType :: env, s1)
    removeTypeInEnv(Nil(), argType, env, deriveType(argType :: env, s1).get)

    val s2 = TermTr.shift(s1, -1, 0)
    deriveTypeValidity(env, s2)

  }.ensuring(
    deriveType(env, absSubstitution(absTd.ter.body, argTd.term)).isDefined &&
    (typ == deriveType(env, absSubstitution(absTd.ter.body, argTd.term)).get.t)
  )

  @opaque @pure
  def absDerivationInversion(td: TypeDerivation): Unit = {
    require(td.term.isInstanceOf[Abs])
  }.ensuring(td.isInstanceOf[AbsDerivation])

  @opaque @pure
  def reductionPreservationTheorem(td: TypeDerivation, reduced: Term): Unit = {
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

            reductionPreservationTheorem(td1, t1p)
            val td1p = deriveType(env, t1p).get
            deriveTypeValidity(env, t1p)

            val tdp = AppDerivation(env, typ, tp, td1p, td2)
            
            assert(tdp.isValid)
            deriveTypeCompleteness(tdp)

            assert(deriveType(td.env, reduced).get === td)
          }
          case App2Congruence => {
            app2CongruenceInversion(t, reduced)
            val tp = reduced.asInstanceOf[App]
            val t2p = tp.t2
            
            reductionPreservationTheorem(td2, t2p)
            val td2p = deriveType(env, t2p).get
            deriveTypeValidity(env, t2p)

            val tdp = AppDerivation(env, typ, tp, td1, td2p)
            assert(tdp.isValid)
            deriveTypeCompleteness(tdp)

            assert(deriveType(td.env, reduced).get === td)
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

            reductionPreservationTheorem(ftd, fp)
            val ftdp = deriveType(env, fp).get
            deriveTypeValidity(env, fp)

            val tdp = FixDerivation(env, typ, tp, ftdp)
            
            assert(tdp.isValid)
            deriveTypeCompleteness(tdp)

            assert(deriveType(td.env, reduced).get === td)
          }
          case AbsFixReduction => {
            absFixReductionInversion(t, reduced)
            absDerivationInversion(ftd)
            preservationUnderAbsSubst(env, ftd.asInstanceOf[AbsDerivation], td, typ)
          }
        }
      }
      case TAppDerivation(env, typ, TApp(body, typeArg), btd) => {
        aSsUmE(
          deriveType(td.env, reduced).isDefined &&
          (deriveType(td.env, reduced).get === td)
        )
      }
    }

  }.ensuring( 
    deriveType(td.env, reduced).isDefined &&
    (deriveType(td.env, reduced).get === td)
  )

}