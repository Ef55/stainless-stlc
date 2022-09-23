import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Kinding {
  import LambdaOmega._

  sealed trait KindDerivation {

    def env: KindEnvironment = this match {
      case BasicTypeDerivation(e, _, _) => e
      case VariableTypeDerivation(e, _, _) => e
      case AbsTypeDerivation(e, _, _, _) => e
      case AppTypeDerivation(e, _, _, _, _) => e
      case ArrowTypeDerivation(e, _, _, _, _) => e

    }

    def k: Kind = this match {
      case BasicTypeDerivation(_, k, _) => k
      case VariableTypeDerivation(_, k, _) => k
      case AbsTypeDerivation(_, k, _, _) => k
      case AppTypeDerivation(_, k, _, _, _) => k
      case ArrowTypeDerivation(_, k, _, _, _) => k
    }

    def typ: Type = this match{
      case BasicTypeDerivation(_, _, typ) => typ
      case VariableTypeDerivation(_, _, typ) => typ
      case AbsTypeDerivation(_, _, typ, _) => typ
      case AppTypeDerivation(_, _, typ, _, _) => typ
      case ArrowTypeDerivation(_, _, typ, _, _) => typ
    }

    def isValid: Boolean = {
      this match{
        case BasicTypeDerivation(_, k, _) => k == ProperKind
        case VariableTypeDerivation(env, k, VariableType(j)) => {
          (j < env.size) &&
          env(j) == k
        }
        case ArrowTypeDerivation(_, k, ArrowType(t1, t2), bkd1, bkd2) => {
          bkd1.isValid && bkd2.isValid && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ProperKind && bkd2.k == ProperKind && k == ProperKind
        }
        case AbsTypeDerivation(env, ArrowKind(k1, k2), AbsType(argK, body), bkd) => {
          bkd.isValid && // Premise is valid,
          bkd.typ == body && bkd.env == argK :: env && // and has matching attributes
          argK == k1 && bkd.k == k2 // Types are correct
        }
        case AbsTypeDerivation(_ ,_, _, _) => false // An abstraction should always have an arrow type...
        case AppTypeDerivation(env, k, AppType(t1, t2), bkd1, bkd2) => {
          bkd1.isValid && bkd2.isValid && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ArrowKind(bkd2.k, k) // The body has expected type
        }
      }
    }
    
    def ===(that: KindDerivation): Boolean = {
      this.k == that.k && this.env == that.env
    }
  }
  case class BasicTypeDerivation(e: KindEnvironment, k: Kind, typ: BasicType) extends KindDerivation
  case class VariableTypeDerivation(e: KindEnvironment, k: Kind, typ: VariableType) extends KindDerivation
  case class AbsTypeDerivation(e: KindEnvironment, k: Kind, typ: AbsType, bkd: KindDerivation) extends KindDerivation
  case class AppTypeDerivation(e: KindEnvironment, k: Kind, typ: AppType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation
  case class ArrowTypeDerivation(e: KindEnvironment, k: Kind, typ: ArrowType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation

  def deriveKind(env: KindEnvironment, t: Type): Option[KindDerivation] = {
    t match {
      case bt@BasicType(_) => Some(BasicTypeDerivation(env, ProperKind, bt))
      case v@VariableType(j) => if (j < env.size) Some(VariableTypeDerivation(env, env(j), v)) else None()
      case arr@ArrowType(t1, t2) => {
        (deriveKind(env, t1), deriveKind(env, t2)) match {
          case (Some(kd1), Some(kd2)) => {
            if(kd1.k == ProperKind && kd1.k == ProperKind){
              Some(ArrowTypeDerivation(env, ProperKind, arr, kd1, kd2))
            }
            else{
              None()
            }
          }
          case (_, _) => None()
        }
      }
      case abs@AbsType(argK, body) => {
        deriveKind(argK :: env, body) match {
          case None() => None()
          case Some(kb) => Some(AbsTypeDerivation(env, ArrowKind(argK, kb.k), abs, kb))
        }
      }
      case app@AppType(t1, t2) => {
        (deriveKind(env, t1), deriveKind(env, t2)) match {
          case (Some(kd1), Some(kd2)) => {
            kd1.k match{
              case ArrowKind(argK, bodyK) if (argK == kd2.k) => 
                Some(AppTypeDerivation(env, bodyK, app, kd1, kd2))
              case _ => None()
            }
          }
          case (_, _) => None()
        }
      }
    }
  }
  
  def deriveKind(t: Type): Option[KindDerivation] = {
    deriveKind(Nil(), t)
  }

 }


// object TypingProperties {
//   import STLC._
//   import Typing._
//   import Reduction._  
//   import Transformations.{ Terms => TermTr}

//   import ListProperties._
//   import STLCProperties.{ Terms => TermProp}
//   import ReductionProperties._
//   import TransformationsProperties.{ Terms => TermTrProp}


//   /// Type derivations
//   @opaque @pure
//   def deriveTypeCompleteness(@induct td: TypeDerivation): Unit = {
//     require(td.isValid)
//   }.ensuring(deriveType(td.env, td.term) == Some(td))

//   @opaque @pure
//   def deriveTypeSoundness(env: TypeEnvironment, t: Term): Unit = {
//     require(deriveType(env, t).isDefined)
//     t match {
//       case Var(_) => ()
//       case Abs(targ, body) => {
//         deriveTypeSoundness(targ :: env, body)
//       }
//       case App(t1, t2) => {
//         deriveTypeSoundness(env, t1)
//         deriveTypeSoundness(env, t2)
//       }
//       case Fix(f) => {
//         deriveTypeSoundness(env, f)
//       }
//     }
//   }.ensuring(
//     deriveType(env, t).get.isValid && 
//     deriveType(env, t).get.term == t && 
//     deriveType(env, t).get.env == env
//   )

//   @opaque @pure
//   def typeDerivationsUniqueness(td1: TypeDerivation, td2: TypeDerivation): Unit = {
//     require(td1.isValid)
//     require(td2.isValid)
//     require(td1.term == td2.term)
//     require(td1.env == td2.env)

//     deriveTypeCompleteness(td1)
//     deriveTypeCompleteness(td2)
//   }.ensuring(td1 == td2)

//   /// Progress
//   @opaque @pure
//   def callByValueProgress(t: Term): Unit = {
//     require(deriveType(Nil(), t).isDefined)
//     t match{
//       case Var(_) => ()
//       case Abs(_, _) => ()
//       case App(t1, t2) => {
//         callByValueProgress(t1)
//         callByValueProgress(t2) 
//       }
//       case Fix(f) => callByValueProgress(f)
//     }
//   }.ensuring(reduceCallByValue(t).isDefined || t.isValue)


//   /// Preservation

//   @opaque @pure
//   def environmentWeakening(td: TypeDerivation, envExt: TypeEnvironment): TypeDerivation = {
//     require(td.isValid)
//     td match {
//       case VarDerivation(env, typ, Var(k)) => {
//         concatFirstIndexing(env, envExt, k)
//         VarDerivation(env ++ envExt, typ, Var(k))
//       }
//       case AbsDerivation(env, typ, Abs(argType, body), btd) => {
//         val resBtd = environmentWeakening(btd, envExt)
//         AbsDerivation(env ++ envExt, typ, Abs(argType, body), resBtd)
//       }
//       case AppDerivation(env, typ, App(t1, t2), bt1, bt2) => {
//         val resBt1 = environmentWeakening(bt1, envExt)
//         val resBt2 = environmentWeakening(bt2, envExt)
//         AppDerivation(env ++ envExt, typ, App(t1, t2), resBt1, resBt2)
//       }
//       case FixDerivation(env, typ, Fix(f), ftd) => {
//         val resFtd = environmentWeakening(ftd, envExt)
//         FixDerivation(env ++ envExt, typ, Fix(f), resFtd)
//       }
//     }
//   }.ensuring(res => 
//     res.isValid && 
//     ( res.env == td.env ++ envExt ) && 
//     ( res.term == td.term ) && 
//     ( res.t == td.t )
//   )

//   @opaque @pure
//   def variableEnvironmentStrengthening(v: VarDerivation, env: TypeEnvironment, envExt: TypeEnvironment): TypeDerivation = {
//     require(v.env == env ++ envExt)
//     require(v.isValid)
//     require(v.ter.k < env.length)
//     concatFirstIndexing(env, envExt, v.ter.k)
//     VarDerivation(env, v.typ, v.ter)
//   }.ensuring(res => 
//     res.isValid && 
//     ( res.env == env ) && 
//     ( res.t == v.t ) && 
//     ( res.term == v.term )
//   )

//   @opaque @pure
//   def variableEnvironmentUpdate(v: VarDerivation, env: TypeEnvironment, oldEnv: TypeEnvironment, newEnv: TypeEnvironment): TypeDerivation = {
//     require(v.env == env ++ oldEnv)
//     require(v.isValid)
//     require(v.ter.k < env.length)  
//     val v2 = variableEnvironmentStrengthening(v, env, oldEnv) 
//     environmentWeakening(v2, newEnv)
//   }.ensuring(res => 
//     res.isValid && 
//     ( res.env == (env ++ newEnv) ) && 
//     ( res.t == v.t ) && 
//     ( res.term == v.term )
//   )

//   @opaque @pure
//   def insertTypeInEnv(env1: TypeEnvironment, insert: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
//     require(td.isValid)
//     require(env1 ++ env2 == td.env)

//     val newEnv = env1 ++ (insert :: env2)

//     td match {
//       case v@VarDerivation(_, typ, Var(k)) => {
//         if (k < env1.size){
//           variableEnvironmentUpdate(v, env1, env2, insert :: env2)
//         }
//         else{
//           insertionIndexing(env1, env2, insert, k)
//           VarDerivation(newEnv, typ, Var(k + 1))
//          }
//       }
//       case AbsDerivation(_, typ, Abs(argType, body), btd) => {
//         val resBtd = insertTypeInEnv(argType :: env1, insert, env2, btd)
//         AbsDerivation(newEnv, typ, Abs(argType, resBtd.term), resBtd)
//       }
//       case AppDerivation(_, typ, App(t1, t2), td1, td2) => {
//         val resTd1 = insertTypeInEnv(env1, insert, env2, td1)
//         val resTd2 = insertTypeInEnv(env1, insert, env2, td2)
//         AppDerivation(newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)
//       }
//       case FixDerivation(_, typ, Fix(f), ftd) => {
//         val resFtd = insertTypeInEnv(env1, insert, env2, ftd)
//         FixDerivation(newEnv, typ, Fix(resFtd.term), resFtd)
//       }
//     }
    
//   }.ensuring(res =>
//     res.isValid &&
//     ( res.term == TermTr.shift(td.term, 1, env1.size) ) &&
//     ( res.env == env1 ++ (insert :: env2) ) &&
//     ( td.t == res.t )
//   )

//   @opaque @pure
//   def removeTypeInEnv(env1: TypeEnvironment, remove: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
//     require(td.isValid)
//     require(td.env == env1 ++ (remove :: env2))
//     require(!td.term.hasFreeVariablesIn(env1.size, 1))

//     val newEnv = env1 ++ env2

//     td match {
//       case v@VarDerivation(_, typ, Var(k)) => {
//         if (k < env1.size){
//           val res = variableEnvironmentUpdate(v, env1, remove :: env2, env2)
//           res
//         }
//         else{
//           insertionIndexing(env1, env2, remove, k - 1)
//           val res = VarDerivation(newEnv, typ, Var(k - 1))
//           res
//          }
//       }
//       case AbsDerivation(_, typ, Abs(argType, body), btd) => {
//         val resBtd = removeTypeInEnv(argType :: env1, remove, env2, btd)
//         val res = AbsDerivation(newEnv, typ, Abs(argType, resBtd.term), resBtd)
//         res
//       }
//       case AppDerivation(_, typ, App(t1, t2), td1, td2) => {
//         val resTd1 = removeTypeInEnv(env1, remove, env2, td1)
//         val resTd2 = removeTypeInEnv(env1, remove, env2, td2)
//         val res = AppDerivation(newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)
//         res
//       }
//       case FixDerivation(_, typ, Fix(f), ftd) => {
//         val resFtd = removeTypeInEnv(env1, remove, env2, ftd)
//         val res = FixDerivation(newEnv, typ, Fix(resFtd.term), resFtd)
//         res
//       }
//     }
//   }.ensuring(res =>
//     res.isValid &&
//     ( res.term == TermTr.shift(td.term, -1, env1.size) ) &&
//     ( res.env == env1 ++ env2 ) &&
//     ( td.t == res.t)
//   )



//   @opaque @pure
//   def absDerivationInversion(td: TypeDerivation): Unit = {
//     require(td.term.isInstanceOf[Abs])
//   }.ensuring(td.isInstanceOf[AbsDerivation])


//   @opaque @pure
//   def preservationUnderSubst(td: TypeDerivation, j: BigInt, sd: TypeDerivation): TypeDerivation = {
//     require(td.isValid)
//     require(sd.isValid)
//     require(td.env == sd.env)
//     require(0 <= j && j < td.env.size)
//     require(td.env(j) == sd.t)

//     val result = TermTr.substitute(td.term, j, sd.term)

//     td match {
//       case VarDerivation(env, typ, Var(k)) => {
//         if(j == k) {
//           assert(result == sd.term)
//           sd
//         }
//         else {
//           assert(result == td.term)
//           td
//         }
//       }
//       case AbsDerivation(env, typ, Abs(argType, body), btd) => {
//         val d0 = insertTypeInEnv(Nil(), argType, td.env, sd)
//         assert(btd.env == argType :: td.env)
//         val d1 = preservationUnderSubst(btd, j+1, d0) // Fragile: require 3/5
//         val res = AbsDerivation(env, typ, Abs(argType, d1.term), d1)
//         assert(  res.isValid )
//         assert( res.term == TermTr.substitute(td.term, j, sd.term) )
//         assert( td === res )
//         res
//       }
//       case AppDerivation(env, typ, App(t1, t2), td1, td2) => {
//         val td1p = preservationUnderSubst(td1, j, sd)
//         val td2p = preservationUnderSubst(td2, j, sd)
//         val res = AppDerivation(env, typ, App(td1p.term, td2p.term), td1p, td2p)
//         assert(  res.isValid )
//         assert( res.term == TermTr.substitute(td.term, j, sd.term) )
//         assert( td === res )
//         res
//       }
//       case FixDerivation(env, typ, Fix(f), ftd) => {
//         val ftdp = preservationUnderSubst(ftd, j, sd)
//         val res = FixDerivation(env, typ, Fix(ftdp.term), ftdp)
//         assert(  res.isValid )
//         assert( res.term == TermTr.substitute(td.term, j, sd.term) )
//         assert( td === res )
//         res
//       }
//     }

//   }.ensuring(res =>
//     res.isValid &&
//     ( res.term == TermTr.substitute(td.term, j, sd.term) ) &&
//     ( td === res )
//   )

//   @opaque @pure
//   def preservationUnderAbsSubst(env: TypeEnvironment, absTd: AbsDerivation, argTd: TypeDerivation, typ: Type): TypeDerivation = {
//     require(absTd.isValid && argTd.isValid)
//     require(absTd.env == env && argTd.env == env)
//     require(absTd.ter.argType == argTd.t)
//     require(absTd.t == ArrowType(argTd.t, typ))

//     val Abs(argType, _) = absTd.term

//     val sd0 = argTd
//     val sd1 = insertTypeInEnv(Nil(), argType, sd0.env, sd0)
//     val sd2 = preservationUnderSubst(absTd.btd, 0, sd1)

//     assert(!sd0.term.hasFreeVariablesIn(0, 0))
//     TermTrProp.boundRangeShift(sd0.term, 1, 0, 0, 0)
//     TermTrProp.boundRangeSubstitutionLemma(absTd.btd.term, 0, sd1.term)
//     removeTypeInEnv(Nil(), argType, env, sd2)
//   }.ensuring(res => 
//     res.isValid &&
//     ( res.term == absSubstitution(absTd.ter.body, argTd.term) ) &&
//     ( res.env == env ) &&
//     ( res.t == typ )
//   )

//   @opaque @pure
//   def preservation(td: TypeDerivation, reduced: Term): TypeDerivation = {
//     require(td.isValid)
//     require(reducesTo(td.term, reduced).isDefined)
//     decreases(td)

//     val Some(rule) = reducesTo(td.term, reduced)

//     td match {
//       case AbsDerivation(env, typ, t@Abs(argType, body), btd) => {
//         absReducesToSoundness(t, reduced)
//         assert(rule == AbsCongruence)
//         absCongruenceInversion(t, reduced)
//         val tp = reduced.asInstanceOf[Abs]
//         val btdp = preservation(btd, tp.body)
//         val tdp = AbsDerivation(env, typ, tp, btdp)
//         assert(btdp.isValid)
//         assert(btdp.term == tp.body)
//         assert(btd.env == argType :: td.env)
//         assert(btdp.env == btd.env)
//         assert(typ.isInstanceOf[ArrowType])
//         val ArrowType(t1, t2) = typ
//         assert(t1 == argType)
//         assert(t2 == btdp.t)
//         assert(tp == Abs(argType, btdp.term))
//         assert(tdp.isValid)
//         tdp
//       }
//       case AppDerivation(env, typ, t@App(t1, t2), td1, td2) => {

//         assert(td.term == t)
//         appReducesToSoundness(t, reduced)
//         rule match {
//           case App1Congruence => {
//             app1CongruenceInversion(t, reduced)
//             val tp = reduced.asInstanceOf[App]
//             val t1p = tp.t1

//             val td1p = preservation(td1, t1p)
//             val tdp = AppDerivation(env, typ, tp, td1p, td2)
//             assert(td1p.isValid && td2.isValid)
//             assert(tp == App(td1p.term, td2.term))
//             assert(tdp.isValid)
//             tdp
//           }
//           case App2Congruence => {
//             app2CongruenceInversion(t, reduced)
//             val tp = reduced.asInstanceOf[App]
//             val t2p = tp.t2
            
//             val td2p = preservation(td2, t2p)
//             val tdp = AppDerivation(env, typ, tp, td1, td2p)
//             assert(tdp.isValid)
//             tdp
//           }
//           case AbsAppReduction => {
//             absAppReductionInversion(t, reduced)
//             absDerivationInversion(td1)
//             preservationUnderAbsSubst(env, td1.asInstanceOf[AbsDerivation], td2, typ)
//           }
//         }
//       }
//       case FixDerivation(env, typ, t@Fix(f), ftd) => {

//         assert(td.term == t)
//         fixReducesToSoundness(t, reduced)
//         rule match {
//           case FixCongruence => {
//             fixCongruenceInversion(t, reduced)
//             val tp = reduced.asInstanceOf[Fix]
//             val fp = tp.t

//             val ftdp = preservation(ftd, fp)
//             val tdp = FixDerivation(env, typ, tp, ftdp)
//             assert(tdp.isValid)
//             tdp
//           }
//           case AbsFixReduction => {
//             absFixReductionInversion(t, reduced)
//             absDerivationInversion(ftd)
//             preservationUnderAbsSubst(env, ftd.asInstanceOf[AbsDerivation], td, typ)
//           }
//         }
//       }
//     }

//   }.ensuring(res => 
//     res.isValid &&
//     ( res.term == reduced ) &&
//     ( res === td )
//   )

// }