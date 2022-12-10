import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._


import LambdaOmega._
import Kinding._
import ParallelTypeReduction._


object Typing {

  import ARS._

  sealed trait TypeDerivation {

    def env: TypeEnvironment = this match {
      case VarTypingDerivation(e, _, _) => e
      case AbsTypingDerivation(e, _, _, _, _) => e
      case AppTypingDerivation(e, _, _, _, _) => e
      case EquivTypingDerivation(e, _, _, _, _, _) => e
    }

    def t: Type = this match {
      case VarTypingDerivation(_, t, _) => t
      case AbsTypingDerivation(_, t, _, _, _) => t
      case AppTypingDerivation(_, t, _, _, _) => t
      case EquivTypingDerivation(_, t, _, _, _, _) => t
    }

    def term: Term = this match{
      case VarTypingDerivation(_, _, term) => term
      case AbsTypingDerivation(_, _, term, _, _) => term
      case AppTypingDerivation(_, _, term, _, _) => term
      case EquivTypingDerivation(_, _, term, _, _, _) => term
    }

    def isSound: Boolean = {
      this match{
        case VarTypingDerivation(env, t, Var(k)) => {
          (k < env.size) && // Variable in environment
          env(k) == t       // and has the correct type
        }
        case AbsTypingDerivation(env, ArrowType(typ1, typ2), Abs(typ, body), kd, btd) => {
          btd.isSound && // Premise is valid,
          btd.term == body && btd.env == typ :: env && // and has matching attributes
          typ == typ1 && btd.t == typ2 && // Types are correct
          kd.isSound && kd.typ == typ1 && kd.k == ProperKind && kd.env == Nil()
        }
        case AbsTypingDerivation(_ ,_, _, _, _) => false // An abstraction should always have an arrow type...
        case AppTypingDerivation(env, t, App(t1, t2), btd1, btd2) => {
          btd1.isSound && btd2.isSound && // Premises are valid
          btd1.term == t1 && btd2.term == t2 && btd1.env == env && btd2.env == env && // and have matching attributes
          btd1.t == ArrowType(btd2.t, t) // The body has expected type
        }
        case EquivTypingDerivation(env, typ, ter, td, eq, kd) => {
          td.isSound && eq.isValid && kd.isSound && // Premise is valid
          td.env == env && td.term == ter && // and has matching attributes
          eq.t1 == td.t && eq.t2 == typ &&
          kd.env == Nil() && kd.typ == typ && kd.k == ProperKind
        }
      }
    }
    
    def ===(that: TypeDerivation): Boolean = {
      this.t == that.t && this.env == that.env
    }
  }
  case class VarTypingDerivation(e: TypeEnvironment, typ: Type, ter: Var) extends TypeDerivation
  case class AbsTypingDerivation(e: TypeEnvironment, typ: Type, ter: Abs, kd: KindDerivation, btd: TypeDerivation) extends TypeDerivation
  case class AppTypingDerivation(e: TypeEnvironment, typ: Type, ter: App, btd1: TypeDerivation, btd2: TypeDerivation) extends TypeDerivation
  case class EquivTypingDerivation(e: TypeEnvironment, typ: Type, ter: Term, td: TypeDerivation, equiv: ParallelEquivalence, kd: KindDerivation) extends TypeDerivation

  // def deriveType(env: TypeEnvironment, t: Term): Option[TypeDerivation] = {
  //   t match {
  //     case v@Var(k) => if (k < env.size) Some(VarTypingDerivation(env, env(k), v)) else None()
  //     case abs@Abs(targ, body) => {
  //       val k1 = deriveKind(targ)
  //       val tb = deriveType(targ :: env, body)
  //       (k1, tb) match {
  //         case (_, None()) => None()
  //         case (ProperKind, Some(tb)) => Some(AbsTypingDerivation(env, ArrowType(targ, tb.t), abs, tb))
  //       }
  //     }
  //     case app@App(t1, t2) => {
  //       (deriveType(env, t1), deriveType(env, t2)) match {
  //         case (Some(ts1), Some(ts2)) => {
  //           ts1.t match{
  //             case ArrowType(targ, tres) if (targ == ts2.t) => 
  //               Some(AppTypingDerivation(env, tres, app, ts1, ts2))
  //             case _ => None()
  //           }
  //         }
  //         case (_, _) => None()
  //       }
  //     }
  //     case 

  //   }
  // }
  
//   def deriveType(t: Term): Option[TypeDerivation] = {
//     deriveType(Nil(), t)
//   }

}


object TypingProperties {
  import Typing._
  import EvalTermReduction._  
  import ListProperties._
  import Kinding._
  import KindingProperties._
  import ARS._


//   /// Type derivations
//   @opaque @pure
//   def deriveTypeCompleteness(@induct td: TypeDerivation): Unit = {
//     require(td.isSound)
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
//     deriveType(env, t).get.isSound && 
//     deriveType(env, t).get.term == t && 
//     deriveType(env, t).get.env == env
//   )

//   @opaque @pure
//   def typeDerivationsUniqueness(td1: TypeDerivation, td2: TypeDerivation): Unit = {
//     require(td1.isSound)
//     require(td2.isSound)
//     require(td1.term == td2.term)
//     require(td1.env == td2.env)

//     deriveTypeCompleteness(td1)
//     deriveTypeCompleteness(td2)
//   }.ensuring(td1 == td2)

//   /// Progress
  @pure
  def callByValueProgress(td: TypeDerivation): Unit = {
    require(td.isSound)
    require(td.env.isEmpty)
    td match
      case VarTypingDerivation(_, _, _) => ()
      case AbsTypingDerivation(_, _, _, _, _) => ()
      case AppTypingDerivation(_, _, _, btd1, btd2) => 
        callByValueProgress(btd1)
        callByValueProgress(btd1)
      case EquivTypingDerivation(_, _, _, btd, _, _) => 
        callByValueProgress(btd)
    
  }.ensuring(callByValueReduce(td.term).isDefined || td.term.isValue)


  /// Preservation

  @pure
  def environmentWeakening(td: TypeDerivation, envExt: TypeEnvironment): TypeDerivation = {
    require(td.isSound)
    td match 
      case VarTypingDerivation(env, typ, Var(k)) => 
        concatFirstIndexing(env, envExt, k)
        VarTypingDerivation(env ++ envExt, typ, Var(k))

      case AbsTypingDerivation(env, typ, Abs(argType, body), kd, btd) => 
        val resBtd = environmentWeakening(btd, envExt)
        AbsTypingDerivation(env ++ envExt, typ, Abs(argType, body), kd, resBtd)
      
      case AppTypingDerivation(env, typ, App(t1, t2), bt1, bt2) => 
        val resBt1 = environmentWeakening(bt1, envExt)
        val resBt2 = environmentWeakening(bt2, envExt)
        AppTypingDerivation(env ++ envExt, typ, App(t1, t2), resBt1, resBt2)

      case EquivTypingDerivation(env, typ, ter, td, eq, kd) => 
        val resTd = environmentWeakening(td, envExt)
        EquivTypingDerivation(env ++ envExt, typ, ter, resTd, eq, kd)
      case _ => Unreacheable

  }.ensuring(res => 
    res.isSound && 
    res.env == td.env ++ envExt && 
    res.term == td.term && 
    res.t == td.t
  )

  @pure
  def variableEnvironmentStrengthening(k: BigInt, typ: Type, env: TypeEnvironment, envExt: TypeEnvironment): TypeDerivation = {
    require(0 <= k)
    require(k < env.length)
    require(VarTypingDerivation(env ++ envExt, typ, Var(k)).isSound)
    concatFirstIndexing(env, envExt, k)
    VarTypingDerivation(env, typ, Var(k))
  }.ensuring(res => 
    res.isSound && 
    ( res.env == env ) && 
    ( res.t == typ ) && 
    ( res.term == Var(k) )
  )

  @pure
  def variableEnvironmentUpdate(k: BigInt, typ: Type, env: TypeEnvironment, oldEnv: TypeEnvironment, newEnv: TypeEnvironment): TypeDerivation = {
    require(0 <= k)
    require(k < env.length)
    require(VarTypingDerivation(env ++ oldEnv, typ, Var(k)).isSound) 
    val v2 = variableEnvironmentStrengthening(k, typ, env, oldEnv) 
    environmentWeakening(v2, newEnv)
  }.ensuring(res => 
    res.isSound && 
    ( res.env == (env ++ newEnv) ) && 
    ( res.t == typ ) && 
    ( res.term == Var(k) )
  )

  @opaque @pure
  def insertTypeInEnv(env1: TypeEnvironment, insert: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
    require(td.isSound)
    require(env1 ++ env2 == td.env)

    val newEnv = env1 ++ (insert :: env2)

    td match 
      case VarTypingDerivation(_, typ, Var(k)) => 
        if (k < env1.size) then
          variableEnvironmentUpdate(k, typ, env1, env2, insert :: env2)
        else
          insertionIndexing(env1, env2, insert, k)
          VarTypingDerivation(newEnv, typ, Var(k + 1))

      case AbsTypingDerivation(_, typ, Abs(argType, body), kd, btd) =>
        val resBtd = insertTypeInEnv(argType :: env1, insert, env2, btd)
        AbsTypingDerivation(newEnv, typ, Abs(argType, resBtd.term), kd, resBtd)

      case AppTypingDerivation(_, typ, App(t1, t2), td1, td2) =>
        val resTd1 = insertTypeInEnv(env1, insert, env2, td1)
        val resTd2 = insertTypeInEnv(env1, insert, env2, td2)
        AppTypingDerivation(newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(_, typ, ter, btd, equiv, kd) => 
        val resEtd: TypeDerivation = insertTypeInEnv(env1, insert, env2, btd)
        EquivTypingDerivation(newEnv, typ, resEtd.term, resEtd, equiv, kd)

      case _ => Unreacheable
    
  }.ensuring(res =>
    res.isSound &&
    ( res.term == TermTransformations.shift(td.term, 1, env1.size)) &&
    ( res.env == env1 ++ (insert :: env2) ) &&
    ( td.t == res.t )
  )

  @opaque @pure
  def removeTypeInEnv(env1: TypeEnvironment, remove: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
    require(td.isSound)
    require(td.env == env1 ++ (remove :: env2))
    require(!td.term.hasFreeVariablesIn(env1.size, 1))

    val newEnv = env1 ++ env2

    td match 
      case VarTypingDerivation(_, typ, Var(k)) => 
        if (k < env1.size) then
          variableEnvironmentUpdate(k, typ, env1, remove :: env2, env2)
        else
          insertionIndexing(env1, env2, remove, k - 1)
          VarTypingDerivation(newEnv, typ, Var(k - 1))

      case AbsTypingDerivation(_, typ, Abs(argType, body), kd, btd) => 
        val resBtd = removeTypeInEnv(argType :: env1, remove, env2, btd)
        AbsTypingDerivation(newEnv, typ, Abs(argType, resBtd.term), kd, resBtd)

      case AppTypingDerivation(_, typ, App(t1, t2), td1, td2) => 
        val resTd1 = removeTypeInEnv(env1, remove, env2, td1)
        val resTd2 = removeTypeInEnv(env1, remove, env2, td2)
        AppTypingDerivation(newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(_, typ, ter, btd, equiv, kd) => 
        val resEtd: TypeDerivation = removeTypeInEnv(env1, remove, env2, btd)
        EquivTypingDerivation(newEnv, typ, resEtd.term, resEtd, equiv, kd)

      case _ => Unreacheable
      
  }.ensuring(res =>
    res.isSound &&
    ( res.term == TermTransformations.shift(td.term, -1, env1.size) ) &&
    ( res.env == env1 ++ env2 ) &&
    ( td.t == res.t)
  )


  @opaque @pure
  def preservationUnderSubst(td: TypeDerivation, j: BigInt, sd: TypeDerivation): TypeDerivation = {
    require(td.isSound)
    require(sd.isSound)
    require(td.env == sd.env)
    require(0 <= j && j < td.env.size)
    require(td.env(j) == sd.t)

    val result = TermTransformations.substitute(td.term, j, sd.term)

    td match 
      case VarTypingDerivation(env, typ, Var(k)) => if j == k then sd else td

      case AbsTypingDerivation(env, typ, Abs(argType, body), kd, btd) => 
        val d0 = insertTypeInEnv(Nil(), argType, td.env, sd)
        assert(btd.env == argType :: td.env)
        val d1 = preservationUnderSubst(btd, j+1, d0) // Fragile: require 3/5
        AbsTypingDerivation(env, typ, Abs(argType, d1.term), kd, d1)

      case AppTypingDerivation(env, typ, App(t1, t2), td1, td2) => 
        val td1p = preservationUnderSubst(td1, j, sd)
        val td2p = preservationUnderSubst(td2, j, sd)
        AppTypingDerivation(env, typ, App(td1p.term, td2p.term), td1p, td2p)

      case EquivTypingDerivation(env, typ, term, btd, equiv, kd) => 
        val substD = preservationUnderSubst(btd, j, sd)
        EquivTypingDerivation(env, typ, substD.term, substD, equiv, kd)
      
      case _ => Unreacheable

  }.ensuring(res =>
    res.isSound &&
    ( res.term == TermTransformations.substitute(td.term, j, sd.term) ) &&
    ( td === res )
  )

  @opaque @pure
  def preservationUnderAbsSubst(bodyTd: TypeDerivation, argTd: TypeDerivation): TypeDerivation = {
    require(bodyTd.isSound)
    require(argTd.isSound)
    require(bodyTd.env == argTd.t :: argTd.env)

    val sd1 = insertTypeInEnv(Nil(), argTd.t, argTd.env, argTd)
    val sd2 = preservationUnderSubst(bodyTd, 0, sd1)

    TermTransformationsProperties.boundRangeShift(argTd.term, 1, 0, 0, 0)
    TermTransformationsProperties.boundRangeSubstitutionLemma(bodyTd.term, 0, sd1.term)

    removeTypeInEnv(Nil(), argTd.t, argTd.env, sd2)

  }.ensuring(res => 
    res.isSound &&
    ( res.term == TermTransformations.absSubstitution(bodyTd.term, argTd.term)) &&
    ( res.env == argTd.env ) &&
    ( res.t == bodyTd.t)
  )

  

  def soundTypingHasProperKind(td: TypeDerivation, wf: List[KindDerivation]): KindDerivation = {
    require(td.isSound)
    require(Kinding.isWellFormed(td.env, wf))
    
    td match
      case VarTypingDerivation(env, _, Var(j)) => 
        isWellFormedApply(env, wf, j)
        wf(j)
      case AbsTypingDerivation(_, ArrowType(t1, t2), Abs(argK, _), kd, btd) => ArrowKindingDerivation(Nil(), ProperKind, ArrowType(t1, t2), kd, soundTypingHasProperKind(btd, Cons(kd, wf)))
      case AppTypingDerivation(_, _, _, td1, td2) => 
        val kd1 = soundTypingHasProperKind(td1, wf)
        assert(kd1.typ.isInstanceOf[ArrowType])
        arrowKindingInversion(kd1)
        kd1 match
          case ArrowKindingDerivation(_, _, _, _, kd12) => kd12
          case _ => Unreacheable
      case EquivTypingDerivation(_, _, _, _, _, kd) => kd
      case _ => Unreacheable

  }.ensuring(res => 
    res.isSound &&
    res.env == Nil() &&
    res.typ == td.t &&    
    res.k == ProperKind)

  def inversionStrongLemmaAbs(argT: Type, body: Term, t1: Type, t2: Type, equiv: ParallelEquivalence, td: TypeDerivation, kd: KindDerivation): (ParallelEquivalence, TypeDerivation, KindDerivation) = {
    require(td.term == Abs(argT, body))
    require(td.isSound)
    require(equiv.isValid)
    require(equiv.t1 == td.t)
    require(equiv.t2 == ArrowType(t1, t2))
    require(kd.isSound)
    require(kd.k == ProperKind)
    require(kd.env == Nil())
    require(kd.typ == t2)

    td match
      case EquivTypingDerivation(_, _, _, btd, equiv2, _) =>
        val equivArrow: ParallelEquivalence = ARSTransitivity(equiv2, equiv)
        inversionStrongLemmaAbs(argT, body, t1, t2, equivArrow, btd, kd)
      case AbsTypingDerivation(env, ArrowType(s1, s2), _, kd2, btd) =>
        val (equiv1, equiv2) = ParallelTypeReductionProperties.arrowEquivalence(s1, s2, t1, t2, equiv)
        (ARSSymmetry(equiv1), EquivTypingDerivation(Cons(argT, env), t2, body, btd, equiv2, kd), kd2) 

  }.ensuring(res =>
    res._1.isValid &&
    res._2.isSound &&
    res._3.isSound &&
    res._1.t1 == t1 &&
    res._1.t2 == argT &&
    res._2.env == Cons(argT, td.env) &&
    res._2.t == t2 &&
    res._2.term == body &&
    res._3.env == Nil() &&
    res._3.k == ProperKind &&
    res._3.typ == argT)

  def inversionWeakLemmaAbs(argT: Type, body: Term, t1: Type, t2: Type, td: TypeDerivation, wf: List[KindDerivation]): (ParallelEquivalence, TypeDerivation, KindDerivation) = {
    require(Kinding.isWellFormed(td.env, wf))
    require(td.isSound)
    require(td.t == ArrowType(t1, t2))
    require(td.term == Abs(argT, body))

    val arrowKd = soundTypingHasProperKind(td, wf)
    arrowKindingInversion(arrowKd)
    arrowKd match
      case ArrowKindingDerivation(_, _, _, _, kd2) =>
        inversionStrongLemmaAbs(argT, body, t1, t2, ARSReflexivity(ArrowType(t1, t2)), td, kd2)
      case _ => Unreacheable

  }.ensuring(res =>
    res._1.isValid &&
    res._2.isSound &&
    res._3.isSound &&
    res._1.t1 == t1 &&
    res._1.t2 == argT &&
    res._2.env == Cons(argT, td.env) &&
    res._2.t == t2 &&
    res._2.term == body &&
    res._3.env == Nil() &&
    res._3.k == ProperKind &&
    res._3.typ == argT)

  @opaque @inlineOnce @pure
  def preservation(td: TypeDerivation, red: EvalReductionDerivation, wf: List[KindDerivation]): TypeDerivation = {
    require(td.isSound)
    require(red.isSound)
    require(red.term1 == td.term)
    require(Kinding.isWellFormed(td.env, wf))

    (td, red) match
      case (EquivTypingDerivation(env, typ, term, btd, equiv, kd), _) => 
        val bodyPreservation = preservation(btd, red, wf)
        EquivTypingDerivation(env, typ, bodyPreservation.term, bodyPreservation, equiv, kd)
      case (AbsTypingDerivation(env, typ, Abs(argType, body), kd, btd), AbsDerivation(t1, t2, rd)) => 
        val bodyPreservation = preservation(btd, rd, Cons(kd, wf))
        AbsTypingDerivation(env, typ, t2, kd, bodyPreservation)
      case (AppTypingDerivation(env, typ, App(t11, t12), td1, td2), AppDerivationL(t1, App(t21, t22), brd1)) => 
        val bodyPreservation = preservation(td1, brd1, wf)
        AppTypingDerivation(env, typ, App(t21, t12), bodyPreservation, td2)
      case (AppTypingDerivation(env, typ, App(t11, t12), td1, td2), AppDerivationR(t1, App(t21, t22), brd2)) => 
        val bodyPreservation = preservation(td2, brd2, wf)
        AppTypingDerivation(env, typ, App(t11, t22), td1, bodyPreservation)
      case (AppTypingDerivation(env, typ, App(Abs(argT1, body11), arg11), absTd, td2), AppAbsDerivation(Abs(argT2, body21), arg21)) =>
        absTd.t match
          case ArrowType(t1, t2) => 
            val (equiv, bodyDeriv, kd) = inversionWeakLemmaAbs(argT1, body11, t1, t2, absTd, wf)
            val argDeriv = EquivTypingDerivation(env, argT1, arg11, td2, equiv,kd)
            preservationUnderAbsSubst(bodyDeriv, argDeriv)
          case _ => Unreacheable 
      case _ => Unreacheable
  }.ensuring(res => 
    res.isSound &&
    ( res.term == red.term2 ) &&
    ( res.env == td.env ) &&
    ( res.t == td.t)
  )

}